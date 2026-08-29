import Solcore.Semantics.HostDriverCompletenessProperties

/-! Compile-time regressions for Core and generic-driver replay completeness. -/

set_option autoImplicit false

namespace Solcore.Test.HostDriverCompleteness

open Solcore

namespace Core

private def slot : Solcore.Core.Word := ⟨3, by decide⟩
private def returned : Solcore.Core.Word := ⟨7, by decide⟩

private def requestState : Solcore.Core.State :=
  ⟨.ret (.word slot), [.hostApply .storageRead], []⟩

private def suspension : Solcore.Core.HostSuspension :=
  ⟨.storageRead slot, [], []⟩

private def finalState : Solcore.Core.State :=
  Solcore.Core.State.final (.word returned) []

private theorem request_emission :
    Solcore.Core.HostRequestEmission requestState suspension := by
  exact .storageRead

private theorem resumed :
    suspension.resume returned = finalState := by
  rfl

private def transitionRequestState : Solcore.Core.State :=
  ⟨.ret (.word slot),
    [.hostApply .storageRead, .letBody .unit []], []⟩

private def transitionSuspension : Solcore.Core.HostSuspension :=
  ⟨.storageRead slot, [.letBody .unit []], []⟩

private def resumedTransitionState : Solcore.Core.State :=
  transitionSuspension.resume returned

private def afterResumedTransition : Solcore.Core.State :=
  ⟨.eval .unit [.word returned], [], []⟩

private def transitionFinalState : Solcore.Core.State :=
  Solcore.Core.State.final .unit []

private theorem transition_request_emission :
    Solcore.Core.HostRequestEmission
      transitionRequestState transitionSuspension := by
  exact .storageRead

private theorem resumed_transition_ready :
    Solcore.Core.HostTransition
      resumedTransitionState afterResumedTransition := by
  exact .core .bindLet

private theorem unit_transition_ready :
    Solcore.Core.HostTransition
      afterResumedTransition transitionFinalState := by
  exact .core .unit

private theorem composed_core_path :
    Solcore.Core.HostSteps 2
      resumedTransitionState transitionFinalState := by
  have first :
      Solcore.Core.HostSteps 1
        resumedTransitionState afterResumedTransition :=
    .cons resumed_transition_ready .refl
  have second :
      Solcore.Core.HostSteps 1
        afterResumedTransition transitionFinalState :=
    .cons unit_transition_ready .refl
  exact first.trans second

private theorem request_state_hasType :
    Solcore.Core.HostStateHasType requestState .word [] := by
  exact .ret .nil .word (.cons .hostApply .nil)

private theorem done_replay_of_steps :
    Solcore.Core.hostRun 0 finalState = .done (.word returned) [] := by
  apply Solcore.Core.hostRun_done_complete_of_steps
    (Solcore.Core.HostSteps.refl (state := finalState))
  · rfl
  · omega

private theorem done_replay_final :
    Solcore.Core.hostRun 4 finalState = .done (.word returned) [] := by
  apply Solcore.Core.hostRun_done_complete
    (Solcore.Core.HostSteps.refl (state := finalState))
  omega

private def faultState : Solcore.Core.State :=
  ⟨.ret (.bool true), [.hostApply .storageRead], []⟩

private def fault : Solcore.Core.MachineFault :=
  .invalidHostArgument .storageRead (.bool true)

private theorem fault_replay :
    Solcore.Core.hostRun 2 faultState = .fault fault faultState := by
  apply Solcore.Core.hostRun_fault_complete_of_steps
    (Solcore.Core.HostSteps.refl (state := faultState))
  · rfl
  · omega

private theorem suspension_replay :
    Solcore.Core.hostRun 1 requestState = .suspended suspension 0 := by
  exact Solcore.Core.hostRun_suspended_complete_of_steps
    (Solcore.Core.HostSteps.refl (state := requestState))
    request_emission (by omega)

private theorem outOfFuel_replay :
    Solcore.Core.hostRun 0 requestState = .outOfFuel requestState := by
  apply Solcore.Core.hostRun_outOfFuel_complete
    (Solcore.Core.HostSteps.refl (state := requestState))
  exact .inr ⟨suspension, request_emission⟩

private def transitionState : Solcore.Core.State :=
  Solcore.Core.State.initial .unit

private theorem outOfFuel_transition_replay :
    Solcore.Core.hostRun 0 transitionState = .outOfFuel transitionState := by
  apply Solcore.Core.hostRun_outOfFuel_complete
    (Solcore.Core.HostSteps.refl (state := transitionState))
  exact .inl ⟨Solcore.Core.State.final .unit,
    .core Solcore.Core.Transition.unit⟩

end Core

namespace Driver

private def changingHandler : Solcore.Semantics.HostHandler Nat where
  handle context request :=
    match request with
    | .storageRead _ => (context + 1, Core.returned)
    | .storageWrite _ _ => (context + 1, ())
    | .storageAddress => (context + 1, Core.returned)
    | .codeAddress => (context + 1, Core.returned)
    | .callValue => (context + 1, Core.returned)
    | .callerAddress => (context + 1, Core.returned)

private theorem handled :
    changingHandler.handleSuspension 0 Core.suspension =
      (1, Core.finalState) := by
  rfl

private theorem one_request_path :
    Solcore.Semantics.HostDriver.HandledSteps changingHandler 1
      0 Core.requestState 1 Core.finalState := by
  exact .handle
    (Solcore.Core.HostSteps.refl (state := Core.requestState))
    Core.request_emission handled
    (.core (Solcore.Core.HostSteps.refl (state := Core.finalState)))

private theorem handled_path_preserves_type :
    Solcore.Core.HostStateHasType Core.finalState .word [] :=
  one_request_path.preserve Core.request_state_hasType

private def expected : Solcore.Semantics.HostDriverResult Nat :=
  ⟨1, .done (.word Core.returned) []⟩

private theorem done_complete_exact_context :
    Solcore.Semantics.HostDriver.run changingHandler 0 1 Core.requestState =
      expected := by
  exact Solcore.Semantics.HostDriver.run_done_complete changingHandler
    one_request_path (by omega)

private theorem done_iff_forward :
    expected.FuelSoundWith changingHandler 1 0 Core.requestState := by
  exact
    (Solcore.Semantics.HostDriver.run_eq_iff_fuelSoundWith
      changingHandler 0 1 Core.requestState expected).mp
      done_complete_exact_context

private theorem fuel_sound_hasType :
    expected.outcome.HasType .word [] :=
  done_iff_forward.hasType Core.request_state_hasType

private theorem same_fuel_result_unique
    (result : Solcore.Semantics.HostDriverResult Nat)
    (sound :
      result.FuelSoundWith changingHandler 1 0 Core.requestState) :
    result = expected :=
  sound.result_unique done_iff_forward

private theorem done_fuel_evidence_mono :
    expected.FuelSoundWith changingHandler 8 0 Core.requestState :=
  done_iff_forward.done_mono (by omega)

private theorem done_result_unique_across_fuel
    (finalContext : Nat)
    (value : Solcore.Core.Value)
    (store : Solcore.Core.Store)
    (sound :
      (⟨finalContext, .done value store⟩ :
        Solcore.Semantics.HostDriverResult Nat).FuelSoundWith
          changingHandler 8 0 Core.requestState) :
    (⟨finalContext, .done value store⟩ :
      Solcore.Semantics.HostDriverResult Nat) = expected :=
  sound.done_result_unique done_iff_forward

private theorem done_iff_reverse :
    Solcore.Semantics.HostDriver.run changingHandler 0 1 Core.requestState =
      expected := by
  exact
    (Solcore.Semantics.HostDriver.run_eq_iff_fuelSoundWith
      changingHandler 0 1 Core.requestState expected).mpr
      done_iff_forward

private theorem done_stable :
    Solcore.Semantics.HostDriver.run changingHandler 0 8 Core.requestState =
      expected := by
  exact Solcore.Semantics.HostDriver.run_done_stable changingHandler
    done_complete_exact_context (by omega)

private theorem done_stable_same_fuel :
    Solcore.Semantics.HostDriver.run changingHandler 0 1 Core.requestState =
      expected := by
  exact Solcore.Semantics.HostDriver.run_done_stable changingHandler
    done_complete_exact_context (Nat.le_refl 1)

private theorem done_runtime :
    (Solcore.Semantics.HostDriver.run
      changingHandler 0 8 Core.requestState).context = 1 := by
  native_decide

private theorem done_outcome_runtime :
    (Solcore.Semantics.HostDriver.run
      changingHandler 0 8 Core.requestState).outcome =
        .done (.word Core.returned) [] := by
  native_decide

private theorem handled_before_transition :
    changingHandler.handleSuspension 0 Core.transitionSuspension =
      (1, Core.resumedTransitionState) := by
  rfl

private theorem one_request_outOfFuel_path :
    Solcore.Semantics.HostDriver.HandledSteps changingHandler 1
      0 Core.transitionRequestState 1 Core.resumedTransitionState := by
  exact .handle
    (Solcore.Core.HostSteps.refl (state := Core.transitionRequestState))
    Core.transition_request_emission handled_before_transition
    (.core
      (Solcore.Core.HostSteps.refl (state := Core.resumedTransitionState)))

private theorem post_request_core_path :
    Solcore.Semantics.HostDriver.HandledSteps changingHandler 2
      1 Core.resumedTransitionState 1 Core.transitionFinalState :=
  .core Core.composed_core_path

private theorem composed_handled_path :
    Solcore.Semantics.HostDriver.HandledSteps changingHandler 3
      0 Core.transitionRequestState 1 Core.transitionFinalState :=
  one_request_outOfFuel_path.trans post_request_core_path

private theorem outOfFuel_complete_after_context_update :
    Solcore.Semantics.HostDriver.run
      changingHandler 0 1 Core.transitionRequestState =
        ⟨1, .outOfFuel Core.resumedTransitionState⟩ := by
  apply Solcore.Semantics.HostDriver.run_outOfFuel_complete
    changingHandler one_request_outOfFuel_path
  exact .inl
    ⟨Core.afterResumedTransition, Core.resumed_transition_ready⟩

private theorem done_complete_after_context_update :
    Solcore.Semantics.HostDriver.run
      changingHandler 0 3 Core.transitionRequestState =
        ⟨1, .done .unit []⟩ := by
  exact Solcore.Semantics.HostDriver.run_done_complete
    changingHandler composed_handled_path (by omega)

private theorem outOfFuel_differs_across_fuel :
    Solcore.Semantics.HostDriver.run
        changingHandler 0 1 Core.transitionRequestState ≠
      Solcore.Semantics.HostDriver.run
        changingHandler 0 3 Core.transitionRequestState := by
  rw [outOfFuel_complete_after_context_update,
    done_complete_after_context_update]
  simp

private theorem outOfFuel_after_context_update_runtime :
    (Solcore.Semantics.HostDriver.run
      changingHandler 0 1 Core.transitionRequestState).context = 1 ∧
    (Solcore.Semantics.HostDriver.run
      changingHandler 0 1 Core.transitionRequestState).outcome =
        .outOfFuel Core.resumedTransitionState := by
  native_decide

private theorem fault_complete :
    Solcore.Semantics.HostDriver.run changingHandler 9 0 Core.faultState =
      ⟨9, .fault Core.fault Core.faultState⟩ := by
  apply Solcore.Semantics.HostDriver.run_fault_complete changingHandler
    (.core (Solcore.Core.HostSteps.refl (state := Core.faultState)))
  · rfl
  · omega

private theorem fault_fuel_evidence :
    (⟨9, .fault Core.fault Core.faultState⟩ :
      Solcore.Semantics.HostDriverResult Nat).FuelSoundWith
        changingHandler 0 9 Core.faultState :=
  (Solcore.Semantics.HostDriver.run_eq_iff_fuelSoundWith
    changingHandler 9 0 Core.faultState
      ⟨9, .fault Core.fault Core.faultState⟩).mp fault_complete

private theorem fault_fuel_evidence_mono :
    (⟨9, .fault Core.fault Core.faultState⟩ :
      Solcore.Semantics.HostDriverResult Nat).FuelSoundWith
        changingHandler 8 9 Core.faultState :=
  fault_fuel_evidence.fault_mono (by omega)

private theorem fault_result_unique_across_fuel
    (finalContext : Nat)
    (error : Solcore.Core.MachineFault)
    (faultState : Solcore.Core.State)
    (sound :
      (⟨finalContext, .fault error faultState⟩ :
        Solcore.Semantics.HostDriverResult Nat).FuelSoundWith
          changingHandler 8 9 Core.faultState) :
    (⟨finalContext, .fault error faultState⟩ :
      Solcore.Semantics.HostDriverResult Nat) =
      ⟨9, .fault Core.fault Core.faultState⟩ :=
  sound.fault_result_unique fault_fuel_evidence

private theorem fault_stable :
    Solcore.Semantics.HostDriver.run changingHandler 9 8 Core.faultState =
      ⟨9, .fault Core.fault Core.faultState⟩ := by
  exact Solcore.Semantics.HostDriver.run_fault_stable changingHandler
    fault_complete (by omega)

end Driver

end Solcore.Test.HostDriverCompleteness
