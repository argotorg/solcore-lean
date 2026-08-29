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

private theorem done_runtime :
    (Solcore.Semantics.HostDriver.run
      changingHandler 0 8 Core.requestState).context = 1 := by
  native_decide

private theorem done_outcome_runtime :
    (Solcore.Semantics.HostDriver.run
      changingHandler 0 8 Core.requestState).outcome =
        .done (.word Core.returned) [] := by
  native_decide

private theorem fault_complete :
    Solcore.Semantics.HostDriver.run changingHandler 9 0 Core.faultState =
      ⟨9, .fault Core.fault Core.faultState⟩ := by
  apply Solcore.Semantics.HostDriver.run_fault_complete changingHandler
    (.core (Solcore.Core.HostSteps.refl (state := Core.faultState)))
  · rfl
  · omega

private theorem fault_stable :
    Solcore.Semantics.HostDriver.run changingHandler 9 8 Core.faultState =
      ⟨9, .fault Core.fault Core.faultState⟩ := by
  exact Solcore.Semantics.HostDriver.run_fault_stable changingHandler
    fault_complete (by omega)

end Driver

end Solcore.Test.HostDriverCompleteness
