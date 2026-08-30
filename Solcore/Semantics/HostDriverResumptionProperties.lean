import Solcore.Semantics.HostDriverCompletenessProperties
import Solcore.Semantics.HostDriverResumption

/-! Exact one-shot and split-fuel laws for generic handled host execution. -/

set_option autoImplicit false

namespace Solcore.Semantics

universe u

namespace HostDriver

/--
After exact exhaustion, an additional budget continues from the retained
context and Core state without replaying the prefix.
-/
theorem run_additional_of_outOfFuel
    {Context : Type u}
    (handler : HostHandler Context)
    {context nextContext : Context}
    {fuel additional : Nat}
    {state exhausted : Core.State}
    (execution :
      run handler context fuel state =
        ⟨nextContext, .outOfFuel exhausted⟩) :
    run handler context (fuel + additional) state =
      run handler nextContext additional exhausted := by
  have prefixSound := run_fuelSound handler context fuel state
  rw [execution] at prefixSound
  change
    HandledSteps handler fuel context state nextContext exhausted ∧ _
      at prefixSound
  obtain ⟨prefixPath, _prefixReady⟩ := prefixSound
  have suffixSound :=
    run_fuelSound handler nextContext additional exhausted
  cases suffixExecution : run handler nextContext additional exhausted with
  | mk finalContext outcome =>
      apply run_eq_of_fuelSoundWith handler context
        (fuel + additional) state ⟨finalContext, outcome⟩
      rw [suffixExecution] at suffixSound
      cases outcome with
      | done value store =>
          change ∃ spent, spent ≤ additional ∧ _ at suffixSound
          change ∃ spent, spent ≤ fuel + additional ∧ _
          obtain ⟨spent, bound, suffix⟩ := suffixSound
          exact ⟨fuel + spent, Nat.add_le_add_left bound fuel,
            prefixPath.trans suffix⟩
      | outOfFuel finalState =>
          change
            HandledSteps handler additional nextContext exhausted
                finalContext finalState ∧ _ at suffixSound
          change
            HandledSteps handler (fuel + additional) context state
                finalContext finalState ∧ _
          exact ⟨prefixPath.trans suffixSound.1, suffixSound.2⟩
      | fault error faultState =>
          change ∃ spent, spent ≤ additional ∧ _ ∧ _ at suffixSound
          change ∃ spent, spent ≤ fuel + additional ∧ _ ∧ _
          obtain ⟨spent, bound, suffix, terminal⟩ := suffixSound
          exact ⟨fuel + spent, Nat.add_le_add_left bound fuel,
            prefixPath.trans suffix, terminal⟩
      | unsupported suspension remainingFuel =>
          change ∃ spent requestState, _ at suffixSound
          change ∃ spent requestState, _
          obtain ⟨spent, requestState, accounting, suffix, emission,
            unsupported⟩ := suffixSound
          exact ⟨fuel + spent, requestState, by omega,
            prefixPath.trans suffix, emission, unsupported⟩

end HostDriver

namespace HostDriverResult

/-- Splitting an actual run at any fuel boundary agrees with one larger run. -/
theorem resumeWithFuel_run
    {Context : Type u}
    (handler : HostHandler Context)
    (context : Context)
    (fuel additional : Nat)
    (state : Core.State) :
    (HostDriver.run handler context fuel state).resumeWithFuel
        handler additional =
      HostDriver.run handler context (fuel + additional) state := by
  cases execution : HostDriver.run handler context fuel state with
  | mk finalContext outcome =>
      cases outcome with
      | done value store =>
          simp only [resumeWithFuel_done]
          exact
            (HostDriver.run_done_stable handler execution (by omega)).symm
      | outOfFuel exhausted =>
          simp only [resumeWithFuel_outOfFuel]
          exact
            (HostDriver.run_additional_of_outOfFuel handler execution).symm
      | fault error faultState =>
          simp only [resumeWithFuel_fault]
          exact
            (HostDriver.run_fault_stable handler execution (by omega)).symm
      | unsupported suspension remainingFuel =>
          simp only [resumeWithFuel_unsupported]
          have sound := HostDriver.run_fuelSound handler context fuel state
          rw [execution] at sound
          change ∃ spent requestState, _ at sound
          obtain ⟨spent, requestState, accounting, path, emission,
            unsupported⟩ := sound
          exact (HostDriver.run_unsupported_complete handler path emission
            unsupported (by omega)).symm

/-- Zero additional fuel is an identity for every actual driver result. -/
@[simp] theorem resumeWithFuel_run_zero
    {Context : Type u}
    (handler : HostHandler Context)
    (context : Context)
    (fuel : Nat)
    (state : Core.State) :
    (HostDriver.run handler context fuel state).resumeWithFuel handler 0 =
      HostDriver.run handler context fuel state := by
  simpa using resumeWithFuel_run handler context fuel 0 state

/-- Sequential additions associate for every result under one fixed handler. -/
theorem resumeWithFuel_add
    {Context : Type u}
    (result : HostDriverResult Context)
    (handler : HostHandler Context)
    (first second : Nat) :
    (result.resumeWithFuel handler first).resumeWithFuel handler second =
      result.resumeWithFuel handler (first + second) := by
  cases result with
  | mk context outcome =>
      cases outcome with
      | done value store => rfl
      | outOfFuel state =>
          exact resumeWithFuel_run handler context first second state
      | fault error state => rfl
      | unsupported suspension remainingFuel =>
          simp only [resumeWithFuel_unsupported]
          rw [Nat.add_assoc]

/-- Two additions after an actual run equal the corresponding one-shot run. -/
theorem resumeWithFuel_run_add
    {Context : Type u}
    (handler : HostHandler Context)
    (context : Context)
    (fuel first second : Nat)
    (state : Core.State) :
    resumeWithFuel
        ((HostDriver.run handler context fuel state).resumeWithFuel
          handler first)
        handler second =
      HostDriver.run handler context (fuel + first + second) state := by
  rw [resumeWithFuel_run, resumeWithFuel_run]

/-- Resuming a typed result preserves its result type. -/
theorem resumeWithFuel_hasType
    {Context : Type u}
    {definitions : Core.DataEnvironment}
    {resultType : Core.Ty}
    (result : HostDriverResult Context)
    (handler : HostHandler Context)
    (additional : Nat)
    (typing : result.outcome.HasType resultType definitions) :
    (result.resumeWithFuel handler additional).outcome.HasType
      resultType definitions := by
  cases result with
  | mk context outcome =>
      cases outcome with
      | done value store =>
          simpa only [resumeWithFuel_done] using typing
      | outOfFuel state =>
          simpa only [resumeWithFuel_outOfFuel] using
            HostDriver.run_hasType handler context additional state typing
      | fault error state =>
          exact False.elim typing
      | unsupported suspension remainingFuel =>
          simpa only [resumeWithFuel_unsupported,
            HostDriverOutcome.unsupported_hasType_iff] using typing

/-- Resuming a typed result cannot expose a raw machine fault. -/
theorem resumeWithFuel_ne_fault
    {Context : Type u}
    {definitions : Core.DataEnvironment}
    {resultType : Core.Ty}
    (result : HostDriverResult Context)
    (handler : HostHandler Context)
    (additional : Nat)
    (error : Core.MachineFault)
    (faultState : Core.State)
    (typing : result.outcome.HasType resultType definitions) :
    (result.resumeWithFuel handler additional).outcome ≠
      .fault error faultState := by
  intro fault
  have resumedTyping :=
    resumeWithFuel_hasType result handler additional typing
  rw [fault] at resumedTyping
  exact resumedTyping

end HostDriverResult

end Solcore.Semantics
