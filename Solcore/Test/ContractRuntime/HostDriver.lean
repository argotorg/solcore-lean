import Solcore.ContractRuntime.HostDriver
import Solcore.Core.HostRunner
import Solcore.ContractRuntime.HostStorageContext
import Solcore.ContractRuntime.HostStorageDriver
import Solcore.Core.Primitive
import Solcore.ContractRuntime.HostStorageInputData
import Solcore.ContractRuntime.RuntimeScalars
import Solcore.ContractRuntime.ContractWordCallInput
import Solcore.ContractRuntime.TransactionHostStorage
import Solcore.ContractRuntime.TransactionJournal

/-!
# Host driver tests

Host drivers: replay completeness, fuel resumption, storage contexts, transaction journals and runtime
scalars.
-/

section
-- leanmerge: from Solcore.Test.HostDriverCompleteness
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

private def changingHandler : Solcore.ContractRuntime.HostHandler Nat where
  supports := fun _ => true
  handle context request :=
    match request with
    | .storageRead _ => (context + 1, Core.returned)
    | .storageWrite _ _ => (context + 1, ())
    | .storageAddress => (context + 1, Core.returned)
    | .codeAddress => (context + 1, Core.returned)
    | .callValue => (context + 1, Core.returned)
    | .callerAddress => (context + 1, Core.returned)
    | .inputDataByte? _ => (context + 1, some Core.returned)
    | .inputDataSize => (context + 1, Core.returned)
    | .inputDataWordBE? _ => (context + 1, some Core.returned)
    | .currentAddress => (context + 1, Core.returned)
    | .callContractWord _ _ =>
        (context + 1, .failed Core.returned)
    | .callContractWordWithValue _ _ _ =>
        (context + 1, .failed Core.returned)
    | .createContractWord _ _ _ =>
        (context + 1, .failed Core.returned)
    | .emitLogWord _ _ => (context + 1, ())

private theorem handled :
    changingHandler.handleSuspension 0 Core.suspension =
      (1, Core.finalState) := by
  rfl

private theorem one_request_path :
    Solcore.ContractRuntime.HostDriver.HandledSteps changingHandler 1
      0 Core.requestState 1 Core.finalState := by
  exact .handle
    (Solcore.Core.HostSteps.refl (state := Core.requestState))
    Core.request_emission rfl handled
    (.core (Solcore.Core.HostSteps.refl (state := Core.finalState)))

private theorem handled_path_preserves_type :
    Solcore.Core.HostStateHasType Core.finalState .word [] :=
  one_request_path.preserve Core.request_state_hasType

private def expected : Solcore.ContractRuntime.HostDriverResult Nat :=
  ⟨1, .done (.word Core.returned) []⟩

private theorem done_complete_exact_context :
    Solcore.ContractRuntime.HostDriver.run changingHandler 0 1 Core.requestState =
      expected := by
  exact Solcore.ContractRuntime.HostDriver.run_done_complete changingHandler
    one_request_path (by omega)

private theorem done_iff_forward :
    expected.FuelSoundWith changingHandler 1 0 Core.requestState := by
  exact
    (Solcore.ContractRuntime.HostDriver.run_eq_iff_fuelSoundWith
      changingHandler 0 1 Core.requestState expected).mp
      done_complete_exact_context

private theorem fuel_sound_hasType :
    expected.outcome.HasType .word [] :=
  done_iff_forward.hasType Core.request_state_hasType

private theorem same_fuel_result_unique
    (result : Solcore.ContractRuntime.HostDriverResult Nat)
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
        Solcore.ContractRuntime.HostDriverResult Nat).FuelSoundWith
          changingHandler 8 0 Core.requestState) :
    (⟨finalContext, .done value store⟩ :
      Solcore.ContractRuntime.HostDriverResult Nat) = expected :=
  sound.done_result_unique done_iff_forward

private theorem done_iff_reverse :
    Solcore.ContractRuntime.HostDriver.run changingHandler 0 1 Core.requestState =
      expected := by
  exact
    (Solcore.ContractRuntime.HostDriver.run_eq_iff_fuelSoundWith
      changingHandler 0 1 Core.requestState expected).mpr
      done_iff_forward

private theorem done_stable :
    Solcore.ContractRuntime.HostDriver.run changingHandler 0 8 Core.requestState =
      expected := by
  exact Solcore.ContractRuntime.HostDriver.run_done_stable changingHandler
    done_complete_exact_context (by omega)

private theorem done_stable_same_fuel :
    Solcore.ContractRuntime.HostDriver.run changingHandler 0 1 Core.requestState =
      expected := by
  exact Solcore.ContractRuntime.HostDriver.run_done_stable changingHandler
    done_complete_exact_context (Nat.le_refl 1)

private theorem done_runtime :
    (Solcore.ContractRuntime.HostDriver.run
      changingHandler 0 8 Core.requestState).context = 1 := by
  native_decide

private theorem done_outcome_runtime :
    (Solcore.ContractRuntime.HostDriver.run
      changingHandler 0 8 Core.requestState).outcome =
        .done (.word Core.returned) [] := by
  native_decide

private theorem handled_before_transition :
    changingHandler.handleSuspension 0 Core.transitionSuspension =
      (1, Core.resumedTransitionState) := by
  rfl

private theorem one_request_outOfFuel_path :
    Solcore.ContractRuntime.HostDriver.HandledSteps changingHandler 1
      0 Core.transitionRequestState 1 Core.resumedTransitionState := by
  exact .handle
    (Solcore.Core.HostSteps.refl (state := Core.transitionRequestState))
    Core.transition_request_emission rfl handled_before_transition
    (.core
      (Solcore.Core.HostSteps.refl (state := Core.resumedTransitionState)))

private theorem post_request_core_path :
    Solcore.ContractRuntime.HostDriver.HandledSteps changingHandler 2
      1 Core.resumedTransitionState 1 Core.transitionFinalState :=
  .core Core.composed_core_path

private theorem composed_handled_path :
    Solcore.ContractRuntime.HostDriver.HandledSteps changingHandler 3
      0 Core.transitionRequestState 1 Core.transitionFinalState :=
  one_request_outOfFuel_path.trans post_request_core_path

private theorem outOfFuel_complete_after_context_update :
    Solcore.ContractRuntime.HostDriver.run
      changingHandler 0 1 Core.transitionRequestState =
        ⟨1, .outOfFuel Core.resumedTransitionState⟩ := by
  apply Solcore.ContractRuntime.HostDriver.run_outOfFuel_complete
    changingHandler one_request_outOfFuel_path
  exact .inl
    ⟨Core.afterResumedTransition, Core.resumed_transition_ready⟩

private theorem done_complete_after_context_update :
    Solcore.ContractRuntime.HostDriver.run
      changingHandler 0 3 Core.transitionRequestState =
        ⟨1, .done .unit []⟩ := by
  exact Solcore.ContractRuntime.HostDriver.run_done_complete
    changingHandler composed_handled_path (by omega)

private theorem outOfFuel_differs_across_fuel :
    Solcore.ContractRuntime.HostDriver.run
        changingHandler 0 1 Core.transitionRequestState ≠
      Solcore.ContractRuntime.HostDriver.run
        changingHandler 0 3 Core.transitionRequestState := by
  rw [outOfFuel_complete_after_context_update,
    done_complete_after_context_update]
  simp

private theorem outOfFuel_after_context_update_runtime :
    (Solcore.ContractRuntime.HostDriver.run
      changingHandler 0 1 Core.transitionRequestState).context = 1 ∧
    (Solcore.ContractRuntime.HostDriver.run
      changingHandler 0 1 Core.transitionRequestState).outcome =
        .outOfFuel Core.resumedTransitionState := by
  native_decide

private theorem fault_complete :
    Solcore.ContractRuntime.HostDriver.run changingHandler 9 0 Core.faultState =
      ⟨9, .fault Core.fault Core.faultState⟩ := by
  apply Solcore.ContractRuntime.HostDriver.run_fault_complete changingHandler
    (.core (Solcore.Core.HostSteps.refl (state := Core.faultState)))
  · rfl
  · omega

private theorem fault_fuel_evidence :
    (⟨9, .fault Core.fault Core.faultState⟩ :
      Solcore.ContractRuntime.HostDriverResult Nat).FuelSoundWith
        changingHandler 0 9 Core.faultState :=
  (Solcore.ContractRuntime.HostDriver.run_eq_iff_fuelSoundWith
    changingHandler 9 0 Core.faultState
      ⟨9, .fault Core.fault Core.faultState⟩).mp fault_complete

private theorem fault_fuel_evidence_mono :
    (⟨9, .fault Core.fault Core.faultState⟩ :
      Solcore.ContractRuntime.HostDriverResult Nat).FuelSoundWith
        changingHandler 8 9 Core.faultState :=
  fault_fuel_evidence.fault_mono (by omega)

private theorem fault_result_unique_across_fuel
    (finalContext : Nat)
    (error : Solcore.Core.MachineFault)
    (faultState : Solcore.Core.State)
    (sound :
      (⟨finalContext, .fault error faultState⟩ :
        Solcore.ContractRuntime.HostDriverResult Nat).FuelSoundWith
          changingHandler 8 9 Core.faultState) :
    (⟨finalContext, .fault error faultState⟩ :
      Solcore.ContractRuntime.HostDriverResult Nat) =
      ⟨9, .fault Core.fault Core.faultState⟩ :=
  sound.fault_result_unique fault_fuel_evidence

private theorem fault_stable :
    Solcore.ContractRuntime.HostDriver.run changingHandler 9 8 Core.faultState =
      ⟨9, .fault Core.fault Core.faultState⟩ := by
  exact Solcore.ContractRuntime.HostDriver.run_fault_stable changingHandler
    fault_complete (by omega)

end Driver

end Solcore.Test.HostDriverCompleteness
end

section
-- leanmerge: from Solcore.Test.HostDriverResumption
/-! Executable regressions for exact generic-driver fuel resumption. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core
open Solcore.ContractRuntime

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private instance : DecidableEq (HostDriverResult Nat) := by
  intro left right
  cases left with
  | mk leftContext leftOutcome =>
      cases right with
      | mk rightContext rightOutcome =>
          simp only [HostDriverResult.mk.injEq]
          exact inferInstance

private def sameResult
    (left right : HostDriverResult Nat) : Bool :=
  decide (left = right)

private def slot : Word := ⟨3, by decide⟩
private def returned : Word := ⟨7, by decide⟩
private def retained : Word := ⟨11, by decide⟩
private def retainedStore : Store := [.word retained]

/-- Every handled request increments the context, making calls observable. -/
private def countingHandler : HostHandler Nat where
  supports := fun _ => true
  handle count request :=
    match request with
    | .storageRead _ => (count + 1, returned)
    | .storageWrite _ _ => (count + 1, ())
    | .storageAddress => (count + 1, returned)
    | .codeAddress => (count + 1, returned)
    | .callValue => (count + 1, returned)
    | .callerAddress => (count + 1, returned)
    | .inputDataByte? _ => (count + 1, some returned)
    | .inputDataSize => (count + 1, returned)
    | .inputDataWordBE? _ => (count + 1, some returned)
    | .currentAddress => (count + 1, returned)
    | .callContractWord _ _ => (count + 1, .failed returned)
    | .callContractWordWithValue _ _ _ => (count + 1, .failed returned)
    | .createContractWord _ _ _ => (count + 1, .failed returned)
    | .emitLogWord _ _ => (count + 1, ())

/-- A request followed by exactly two ordinary Core transitions. -/
private def requestReady : State :=
  ⟨.ret (.word slot),
    [.hostApply .storageRead, .letBody .unit []], retainedStore⟩

private def postHandler : State :=
  ⟨.ret (.word returned), [.letBody .unit []], retainedStore⟩

private def afterLet : State :=
  ⟨.eval .unit [.word returned], [], retainedStore⟩

private def doneResult : HostDriverResult Nat :=
  ⟨1, .done .unit retainedStore⟩

private def zeroRun : HostDriverResult Nat :=
  HostDriver.run countingHandler 0 0 requestReady

private def afterRequest : HostDriverResult Nat :=
  zeroRun.resumeWithFuel countingHandler 1

private theorem measured_zero_run :
    zeroRun = ⟨0, .outOfFuel requestReady⟩ := by
  native_decide

private theorem measured_request_cost :
    afterRequest = ⟨1, .outOfFuel postHandler⟩ := by
  native_decide

private theorem measured_post_handler_step :
    afterRequest.resumeWithFuel countingHandler 1 =
      ⟨1, .outOfFuel afterLet⟩ := by
  native_decide

private theorem measured_split_completion :
    afterRequest.resumeWithFuel countingHandler 2 = doneResult := by
  native_decide

private theorem measured_one_shot_completion :
    HostDriver.run countingHandler 0 3 requestReady = doneResult := by
  native_decide

private theorem measured_split_one_shot_exact :
    zeroRun.resumeWithFuel countingHandler 3 =
      HostDriver.run countingHandler 0 3 requestReady := by
  native_decide

private theorem measured_actual_run_zero_identity :
    zeroRun.resumeWithFuel countingHandler 0 = zeroRun := by
  native_decide

private theorem measured_sequential_additions :
    (zeroRun.resumeWithFuel countingHandler 1).resumeWithFuel
        countingHandler 2 =
      zeroRun.resumeWithFuel countingHandler (1 + 2) := by
  native_decide

/-- One ordinary step exposes an intentionally ill-typed host argument. -/
private def uncheckedStart : State :=
  ⟨.eval .unit [], [.hostApply .storageRead], retainedStore⟩

private def uncheckedFaultState : State :=
  ⟨.ret .unit, [.hostApply .storageRead], retainedStore⟩

private def uncheckedFault : MachineFault :=
  .invalidHostArgument .storageRead .unit

private def uncheckedZeroRun : HostDriverResult Nat :=
  HostDriver.run countingHandler 13 0 uncheckedStart

private def uncheckedFaultResult : HostDriverResult Nat :=
  ⟨13, .fault uncheckedFault uncheckedFaultState⟩

private theorem measured_unchecked_exhaustion :
    uncheckedZeroRun = ⟨13, .outOfFuel uncheckedStart⟩ := by
  native_decide

private theorem measured_unchecked_split_fault :
    uncheckedZeroRun.resumeWithFuel countingHandler 1 =
      uncheckedFaultResult := by
  native_decide

private theorem measured_unchecked_one_shot_fault :
    HostDriver.run countingHandler 13 1 uncheckedStart =
      uncheckedFaultResult := by
  native_decide

private theorem measured_unchecked_split_one_shot_exact :
    uncheckedZeroRun.resumeWithFuel countingHandler 1 =
      HostDriver.run countingHandler 13 1 uncheckedStart := by
  native_decide

private def completedInput : HostDriverResult Nat :=
  ⟨29, .done (.word returned) retainedStore⟩

private def faultedInput : HostDriverResult Nat :=
  ⟨31, .fault uncheckedFault uncheckedFaultState⟩

private theorem measured_completed_identity :
    completedInput.resumeWithFuel countingHandler 100 = completedInput := by
  native_decide

private theorem measured_faulted_identity :
    faultedInput.resumeWithFuel countingHandler 100 = faultedInput := by
  native_decide

/-- Exercise every result class and compare split runs with measured one-shots. -/
def testHostDriverResumption : IO Unit := do
  assertTrue (sameResult zeroRun ⟨0, .outOfFuel requestReady⟩)
    "zero fuel did not retain the request-ready state"
  assertTrue (sameResult afterRequest ⟨1, .outOfFuel postHandler⟩)
    "one fuel unit did not handle exactly one request before exhaustion"
  assertTrue
    (sameResult (afterRequest.resumeWithFuel countingHandler 1)
      ⟨1, .outOfFuel afterLet⟩)
    "post-handler resumption repeated the request or skipped a Core step"
  assertTrue
    (sameResult
      (afterRequest.resumeWithFuel countingHandler 2) doneResult)
    "post-handler exhaustion did not resume to the exact done result"
  assertTrue
    (sameResult (zeroRun.resumeWithFuel countingHandler 3)
      (HostDriver.run countingHandler 0 3 requestReady))
    "split done execution changed its context, value, or Store"
  assertTrue
    (sameResult (zeroRun.resumeWithFuel countingHandler 0) zeroRun)
    "zero additional fuel changed an actual run result"
  assertTrue
    (sameResult
      ((zeroRun.resumeWithFuel countingHandler 1).resumeWithFuel
        countingHandler 2)
      (zeroRun.resumeWithFuel countingHandler (1 + 2)))
    "two sequential additions differed from their summed addition"
  assertTrue
    (sameResult uncheckedZeroRun ⟨13, .outOfFuel uncheckedStart⟩)
    "zero fuel did not retain the unchecked pre-fault state"
  assertTrue
    (sameResult
      (uncheckedZeroRun.resumeWithFuel countingHandler 1)
      uncheckedFaultResult)
    "resumed unchecked execution did not reach the exact raw fault"
  assertTrue
    (sameResult
      (uncheckedZeroRun.resumeWithFuel countingHandler 1)
      (HostDriver.run countingHandler 13 1 uncheckedStart))
    "split fault execution changed its context, error, or fault state"
  assertTrue
    (sameResult
      (completedInput.resumeWithFuel countingHandler 100) completedInput)
    "resuming a completed input changed its exact bytes"
  assertTrue
    (sameResult
      (faultedInput.resumeWithFuel countingHandler 100) faultedInput)
    "resuming a faulted input changed its exact bytes"

end Tests
end

section
-- leanmerge: from Solcore.Test.HostRuntimeStoreSafety
/-! General host cells preserve capability and location typing through
checker admission, allocation, suspension, and response resumption. -/

set_option autoImplicit false

namespace Tests.HostRuntimeStoreSafety

open Solcore.Core

private def functionType : Ty := .function .word .word

private def zero : Word := ⟨0, by decide⟩

private def storedCapabilityProgram : Program := {
  resultType := .word
  body :=
    .apply
      (.loadCell (.newCell functionType (.var HostFunction.storageRead.index)))
      (.word zero)
}

private theorem storedCapabilityProgram_checked :
    storedCapabilityProgram.checkHost = true := by decide

private theorem storedCapabilityProgram_initial_hasType :
    HostStateHasType (State.initial storedCapabilityProgram.body hostEnvironment) .word :=
  .eval .nil (hostEnvironment_hasTypes [] [])
    (Program.checkHost_sound storedCapabilityProgram_checked) .nil

/-- A capability stored by admitted code is recovered before its host call. -/
example : storedCapabilityProgram.runHostStateful 9 =
    .suspended ⟨.storageRead zero, [], [.hostFunction .storageRead]⟩ 0 := by
  rfl

/-- General cell admission retains finite safety at the host boundary. -/
example (fuel : Nat) (fault : MachineFault) (state : State) :
    storedCapabilityProgram.runHostStateful fuel ≠ .fault fault state :=
  hostRun_never_faults storedCapabilityProgram_initial_hasType

/-- The stored capability survives a response without becoming a pure closure. -/
example (response : Word) :
    HostStateHasType
      ((⟨.storageRead zero, [], [.hostFunction .storageRead]⟩ : HostSuspension).resume response)
      .word := by
  have suspended := hostRun_suspended_hasType storedCapabilityProgram_initial_hasType
    (show hostRun 9 (State.initial storedCapabilityProgram.body hostEnvironment) =
      .suspended ⟨.storageRead zero, [], [.hostFunction .storageRead]⟩ 0 from rfl)
  exact suspended.resume response

/-- A capability can occupy a general cell without being erased to pure typing. -/
example : HostStoreHasTypes [functionType] [.hostFunction .storageRead] := by
  simpa [functionType, HostFunction.functionType, HostFunction.parameterType,
    HostFunction.resultType, Store.allocate] using
    (HostStoreHasTypes.nil (definitions := [])).allocate
      (HostRuntimeValueHasType.hostFunction
        (world := []) (function := .storageRead) (definitions := []))

private def cyclicClosure : Value :=
  .closure .word .word (.apply (.var 2) (.var 0))
    [.cellRef functionType 0, .hostFunction .storageRead]

/-- Typing follows the world lookup, so a closure may capture its own cell. -/
private theorem cyclicClosure_hasType :
    HostRuntimeValueHasType [functionType] cyclicClosure functionType := by
  exact .closure
    (.cons (.cellRef rfl) (.cons .hostFunction .nil))
    (.apply (.var rfl) (.var rfl))

private theorem cyclicStore_hasType :
    HostStoreHasTypes [functionType] [cyclicClosure] where
  length_eq := rfl
  lookup := by
    intro location type found
    cases location with
    | zero =>
        have typeEq : type = functionType := (Option.some.inj found).symm
        subst type
        exact ⟨cyclicClosure, rfl, cyclicClosure_hasType⟩
    | succ location => simp at found

private def callState : State :=
  ⟨.eval (.apply (.var 0) (.word zero)) [cyclicClosure], [], [cyclicClosure]⟩

private theorem callState_hasType : HostStateHasType callState .word :=
  .eval cyclicStore_hasType (.cons cyclicClosure_hasType .nil)
    (.apply (.var rfl) .word) .nil

/-- Every bounded execution remains safe with a capability-capturing cycle. -/
example (fuel : Nat) (fault : MachineFault) (state : State) :
    hostRun fuel callState ≠ .fault fault state :=
  hostRun_never_faults callState_hasType

/-- Host suspension retains the entire cyclic store. -/
example :
    hostRun 10 callState =
      .suspended ⟨.storageRead zero, [], [cyclicClosure]⟩ 0 := by
  rfl

/-- Suspension and resumption keep the same typed world. -/
example (response : Word) :
    HostStateHasType
      ((⟨.storageRead zero, [], [cyclicClosure]⟩ : HostSuspension).resume response)
      .word := by
  have typing : HostSuspensionHasType
      ⟨.storageRead zero, [], [cyclicClosure]⟩ .word :=
    .intro cyclicStore_hasType .nil
  exact typing.resume response

/-- A forged reference is rejected even when its outer value tag is correct. -/
example : ¬ HostRuntimeValueHasType [] (.cellRef .word 0) (.cell .word) := by
  intro typing
  cases typing with
  | cellRef found => simp at found

/-- The stored location type must agree with the reference annotation. -/
example : ¬ HostRuntimeValueHasType [.word] (.cellRef .bool 0) (.cell .bool) := by
  intro typing
  cases typing with
  | cellRef found => contradiction

/-- A store invariant cannot certify a reference outside its world. -/
example : ¬ HostStoreHasTypes [.cell .word] [.cellRef .word 1] := by
  intro typing
  obtain ⟨value, read, valueTyping⟩ := typing.lookup (location := 0) rfl
  have valueEq : value = .cellRef .word 1 := (Option.some.inj read).symm
  subst value
  cases valueTyping with
  | cellRef found => simp at found

end Tests.HostRuntimeStoreSafety
end

section
-- leanmerge: from Solcore.Test.HostStorageContextRebaseWithEffects
/-! Compile-only regressions for joint working-world and effect rebasing. -/

set_option autoImplicit false

namespace Tests.HostStorageContextRebaseWithEffects

open Solcore.ContractRuntime

universe u v

private example
    {RollbackState : Type u} {TraceState : Type v}
    (context : HostStorageDriver.Context RollbackState TraceState)
    (world : WorldState)
    (effects : FrameEffectJournal RollbackState TraceState)
    (account : Account)
    (present :
      world.account? context.context.storageAddress = some account) :
    (HostStorageDriver.Context.rebaseWorkingWithEffects
      context world effects account present).context.storageAddress =
      context.context.storageAddress := by
  simp

private example
    {RollbackState : Type u} {TraceState : Type v}
    (context : HostStorageDriver.Context RollbackState TraceState)
    (world : WorldState)
    (effects : FrameEffectJournal RollbackState TraceState)
    (account : Account)
    (present :
      world.account? context.context.storageAddress = some account) :
    (HostStorageDriver.Context.rebaseWorkingWithEffects
      context world effects account present).context.values.checkpoint =
      context.context.values.checkpoint := by
  simp

private example
    {RollbackState : Type u} {TraceState : Type v}
    (context : HostStorageDriver.Context RollbackState TraceState)
    (world : WorldState)
    (effects : FrameEffectJournal RollbackState TraceState)
    (account : Account)
    (present :
      world.account? context.context.storageAddress = some account) :
    (HostStorageDriver.Context.rebaseWorkingWithEffects
      context world effects account present).context.values.working.1 =
      world := by
  simp

private example
    {RollbackState : Type u} {TraceState : Type v}
    (context : HostStorageDriver.Context RollbackState TraceState)
    (world : WorldState)
    (effects : FrameEffectJournal RollbackState TraceState)
    (account : Account)
    (present :
      world.account? context.context.storageAddress = some account) :
    (HostStorageDriver.Context.rebaseWorkingWithEffects
      context world effects account present).context.values.working.2 =
      effects := by
  simp

end Tests.HostStorageContextRebaseWithEffects
end

section
-- leanmerge: from Solcore.Test.HostStorageDriverResumption
/-! Storage-specialized executable regressions for handled fuel resumption. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core
open Solcore.ContractRuntime

private def codeAddress : Address := ⟨0x10, by decide⟩
private def storageAddress : Address := ⟨0x20, by decide⟩
private def otherAddress : Address := ⟨0x30, by decide⟩
private def callerAddress : Address := ⟨0x40, by decide⟩

private def targetSlot : Word := ⟨0x51, by decide⟩
private def oldValue : Word := ⟨0x52, by decide⟩
private def writtenValue : Word := ⟨0x53, by decide⟩
private def retainedSlot : Word := ⟨0x54, by decide⟩
private def retainedValue : Word := ⟨0x55, by decide⟩
private def otherSlot : Word := ⟨0x61, by decide⟩
private def otherValue : Word := ⟨0x62, by decide⟩
private def checkpointSlot : Word := ⟨0x71, by decide⟩
private def checkpointValue : Word := ⟨0x72, by decide⟩

private def threeByteInput : HostStorageDriver.InputData := {
  bytes := [0x11, 0x22, 0x33].toByteArray
  size_lt_wordModulus := by decide
}

private def oneByteInput : HostStorageDriver.InputData := {
  bytes := [0x11].toByteArray
  size_lt_wordModulus := by decide
}

private def inputsFor
    (inputData : HostStorageDriver.InputData) :
    HostStorageDriver.ExecutionInputs := {
  codeAddress := codeAddress
  callValue := Word.zero
  callerAddress := callerAddress
  inputData := inputData
  currentAddress := codeAddress
}

private def executionInputs := inputsFor threeByteInput
private def changedInputs := inputsFor oneByteInput

/-- Complete a working-storage write before observing an immutable input. -/
private def writeThenInputSizeProgram : Program := {
  resultType := .word
  body :=
    .letE
      (.apply
        (.var HostFunction.storageWrite.index)
        (.pair (.word targetSlot) (.word writtenValue)))
      (.apply (.var (HostFunction.inputDataSize.index + 1)) .unit)
}

private theorem writeThenInputSizeProgram_host_checked :
    writeThenInputSizeProgram.checkHost = true := by
  decide

private def writeThenInputSizeCode : CheckedHostCoreProgram :=
  ⟨writeThenInputSizeProgram, writeThenInputSizeProgram_host_checked⟩

private def selectedStorageAccount : Account :=
  Account.empty
    |>.storageWrite targetSlot oldValue
    |>.storageWrite retainedSlot retainedValue

private def workingWorld : WorldState :=
  WorldState.empty
    |>.putAccount storageAddress selectedStorageAccount
    |>.putAccount otherAddress
      (Account.empty.storageWrite otherSlot otherValue)

private def checkpointWorld : WorldState :=
  WorldState.empty
    |>.putAccount storageAddress
      (Account.empty.storageWrite checkpointSlot checkpointValue)
    |>.putAccount otherAddress
      (Account.empty.storageWrite otherSlot checkpointValue)

private def baseStorageContext :
    FrameCheckpointedWorkingPairWithStorageAddress Nat (List Nat) :=
  ⟨storageAddress,
    ⟨⟨checkpointWorld, ⟨11, [12, 13]⟩⟩,
      (workingWorld, ⟨21, [22, 23]⟩)⟩⟩

private theorem selectedStorageAccount_present :
    baseStorageContext.values.working.1.account?
        baseStorageContext.storageAddress =
      some selectedStorageAccount := by
  rfl

private def baseContext : HostStorageDriver.Context Nat (List Nat) :=
  ⟨baseStorageContext, selectedStorageAccount,
    selectedStorageAccount_present⟩

private def storageValueAt?
    (state : WorldState) (address : Address) (slot : Word) : Option Word :=
  (state.account? address).bind fun account => account.storageValue? slot

private def contextPreserved
    (context : HostStorageDriver.Context Nat (List Nat)) : Bool :=
  let values := context.context.values
  context.context.storageAddress == storageAddress &&
    context.storageAccount.storageValue? retainedSlot == some retainedValue &&
    storageValueAt? values.working.1 otherAddress otherSlot == some otherValue &&
    storageValueAt? values.checkpoint.state storageAddress checkpointSlot ==
      some checkpointValue &&
    storageValueAt? values.checkpoint.state otherAddress otherSlot ==
      some checkpointValue &&
    values.checkpoint.effects.rollback == 11 &&
    values.checkpoint.effects.trace == [12, 13] &&
    values.working.2.rollback == 21 &&
    values.working.2.trace == [22, 23]

private def hasCompletedWrite
    (context : HostStorageDriver.Context Nat (List Nat)) : Bool :=
  context.storageAccount.storageValue? targetSlot == some writtenValue &&
    storageValueAt? context.context.values.working.1
      storageAddress targetSlot == some writtenValue

private def beforeInputSuffix (state : State) : Bool :=
  state.control == .ret .unit &&
    match state.continuation with
    | [.letBody body _] =>
        body ==
          .apply (.var (HostFunction.inputDataSize.index + 1)) .unit
    | _ => false

private def firstFuel : Nat := 10
private def suffixFuel : Nat := 6
private def completionFuel : Nat := 16
private def largerFuel : Nat := 32

private def firstResult :=
  writeThenInputSizeCode.runWithStorage
    baseContext executionInputs firstFuel

private def splitResult :=
  firstResult.resumeWithFuel
    (HostStorageDriver.handler executionInputs) suffixFuel

private def oneShotResult :=
  writeThenInputSizeCode.runWithStorage
    baseContext executionInputs completionFuel

private def largerResult :=
  writeThenInputSizeCode.runWithStorage
    baseContext executionInputs largerFuel

/-- Deliberately outside the same-input theorem: resume with changed input. -/
private def changedInputResume :=
  firstResult.resumeWithFuel
    (HostStorageDriver.handler changedInputs) suffixFuel

private theorem measured_first_exhaustion :
    (match firstResult with
    | { context, outcome := .outOfFuel state } =>
        hasCompletedWrite context &&
          contextPreserved context && beforeInputSuffix state
    | _ => false) = true := by
  native_decide

private theorem measured_one_shot_completion_variant :
    oneShotResult.outcome =
      .done (.word threeByteInput.sizeWord) [] := by
  native_decide

/-- Exact result equality includes context, value, and Core-local Store. -/
private theorem measured_split_one_shot_exact_variant :
    splitResult = oneShotResult := by
  simpa [splitResult, firstResult, oneShotResult, firstFuel,
    suffixFuel, completionFuel] using
    writeThenInputSizeCode.runWithStorage_resumeWithFuel
      baseContext executionInputs firstFuel suffixFuel

private theorem measured_larger_exact :
    largerResult = oneShotResult := by
  have exactOneShot :
      oneShotResult =
        ⟨oneShotResult.context,
          .done (.word threeByteInput.sizeWord) []⟩ := by
    cases resultEq : oneShotResult with
    | mk context outcome =>
        have outcomeEq :
            outcome = .done (.word threeByteInput.sizeWord) [] := by
          simpa [resultEq] using measured_one_shot_completion_variant
        subst outcome
        rfl
  have stable :
      largerResult =
        ⟨oneShotResult.context,
          .done (.word threeByteInput.sizeWord) []⟩ :=
    writeThenInputSizeCode.runWithStorage_done_stable
      (fuel := completionFuel) (largerFuel := largerFuel)
      baseContext executionInputs exactOneShot
      (show completionFuel ≤ largerFuel by decide)
  exact stable.trans exactOneShot.symm

private theorem measured_changed_input_completion :
    changedInputResume.outcome =
      .done (.word oneByteInput.sizeWord) [] := by
  native_decide

/-- A concrete changed-input suffix differs; no general disequality is claimed. -/
private theorem measured_changed_input_changes_suffix :
    changedInputResume.outcome ≠ splitResult.outcome := by
  native_decide

private theorem run_preserves_checkpoint (fuel : Nat) :
    (writeThenInputSizeCode.runWithStorage
      baseContext executionInputs fuel).context.context.values.checkpoint =
        baseContext.context.values.checkpoint := by
  change
    (HostStorageDriver.run baseContext executionInputs fuel
      (State.initial writeThenInputSizeProgram.body hostEnvironment)).context.context.values.checkpoint = _
  exact HostStorageDriver.run_checkpoint baseContext executionInputs fuel _

private theorem run_preserves_working_effects (fuel : Nat) :
    (writeThenInputSizeCode.runWithStorage
      baseContext executionInputs fuel).context.context.values.working.2 =
        baseContext.context.values.working.2 := by
  change
    (HostStorageDriver.run baseContext executionInputs fuel
      (State.initial writeThenInputSizeProgram.body hostEnvironment)).context.context.values.working.2 = _
  exact HostStorageDriver.run_workingEffects
    baseContext executionInputs fuel _

private theorem run_preserves_other_account (fuel : Nat) :
    (writeThenInputSizeCode.runWithStorage
      baseContext executionInputs fuel).context.context.values.working.1.account?
        otherAddress =
      baseContext.context.values.working.1.account? otherAddress := by
  change
    (HostStorageDriver.run baseContext executionInputs fuel
      (State.initial writeThenInputSizeProgram.body hostEnvironment)).context.context.values.working.1.account? otherAddress = _
  exact HostStorageDriver.run_workingAccount?_of_ne_storageAddress
    baseContext executionInputs fuel _ otherAddress (by decide)

def testHostStorageDriverResumption : IO Unit := do
  assertTrue writeThenInputSizeProgram.checkHost
    "the host checker rejected write-then-input-size"

  match firstResult with
  | { context, outcome := .outOfFuel state } =>
      assertTrue (hasCompletedWrite context)
        "fuel 10 exhausted before retaining the working-storage write"
      assertTrue (beforeInputSuffix state)
        "fuel 10 did not stop immediately before the input-sensitive suffix"
      assertTrue (contextPreserved context)
        "the first slice changed checkpoint, effects, or unrelated storage"
  | result =>
      throw (IO.userError
        s!"fuel 10 did not produce the measured exhaustion: {reprStr result.outcome}")

  assertTrue
    (splitResult.outcome ==
      .done (.word threeByteInput.sizeWord) [])
    "same-input resumption returned the wrong value or Store"
  assertTrue
    (oneShotResult.outcome == splitResult.outcome &&
      largerResult.outcome == oneShotResult.outcome)
    "split, one-shot, and larger execution outcomes differed"
  assertTrue
    (hasCompletedWrite splitResult.context &&
      hasCompletedWrite oneShotResult.context &&
      hasCompletedWrite largerResult.context)
    "a completed execution lost the pre-exhaustion write"
  assertTrue
    (contextPreserved splitResult.context &&
      contextPreserved oneShotResult.context &&
      contextPreserved largerResult.context)
    "resumption changed checkpoint, effects, or unrelated storage"

  assertTrue
    (changedInputResume.outcome ==
      .done (.word oneByteInput.sizeWord) [])
    "the deliberately changed-input suffix returned the wrong size"
  assertTrue (changedInputResume.outcome != splitResult.outcome)
    "the concrete changed input did not change the input-sensitive suffix"
  assertTrue
    (hasCompletedWrite changedInputResume.context &&
      contextPreserved changedInputResume.context)
    "the changed-input demonstration lost the retained working context"

end Tests
end

section
-- leanmerge: from Solcore.Test.HostStorageInputData
/-! Executable boundary tests for bounded run input bytes. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core
open Solcore.ContractRuntime
open Solcore.ContractRuntime.HostStorageDriver

private def word (value : Nat) : Word :=
  Word.ofNatModulo value

private def emptyInput : InputData := {
  bytes := [].toByteArray
  size_lt_wordModulus := by decide
}

private def representativeInput : InputData := {
  bytes := [0x12, 0x00, 0xab, 0xff].toByteArray
  size_lt_wordModulus := by decide
}

private def singletonInput : InputData := {
  bytes := [0x7f].toByteArray
  size_lt_wordModulus := by decide
}

private def zeroTailInput : InputData := {
  bytes := [0x11, 0x00].toByteArray
  size_lt_wordModulus := by decide
}

private def shortWordInput : InputData := {
  bytes := (List.replicate 31 (0xa5 : UInt8)).toByteArray
  size_lt_wordModulus := by decide
}

private def exactWordInput : InputData := {
  bytes := ((List.range 32).map UInt8.ofNat).toByteArray
  size_lt_wordModulus := by decide
}

private def slidingWordInput : InputData := {
  bytes := ((List.range 34).map UInt8.ofNat).toByteArray
  size_lt_wordModulus := by decide
}

private def zeroWordInput : InputData := {
  bytes := (List.replicate 32 (0 : UInt8)).toByteArray
  size_lt_wordModulus := by decide
}

private def sequentialWord0 : Word :=
  ⟨0x000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f,
    by decide⟩

private def sequentialWord1 : Word :=
  ⟨0x0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20,
    by decide⟩

private def sequentialWord2 : Word :=
  ⟨0x02030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f2021,
    by decide⟩

/-- An exact natural index beyond machine-word range whose low bits name byte two. -/
private def beyondMachineIndex : Word :=
  ⟨2 ^ 64 + 2, by decide⟩

private theorem observed_byte_lt_256
    (offset result : Word)
    (read : representativeInput.byte? offset = some result) :
    result.val < 256 :=
  InputData.byte?_result_lt_256 representativeInput offset result read

private def allWordBytesCoherent
    (input : InputData) (offset expected : Word) : Bool :=
  (List.range 32).all fun index =>
    input.byte? (word (offset.val + index)) ==
      some ((word index).byteAt expected)

def testHostStorageInputData : IO Unit := do
  assertTrue (emptyInput.sizeWord == word 0)
    "empty input must have exact size zero"
  assertTrue (representativeInput.sizeWord == word 4)
    "the nonempty input size must be represented exactly"
  assertTrue (singletonInput.sizeWord == word 1)
    "a one-byte input must have exact size one"
  assertTrue (zeroTailInput.byte? (word 1) == some Word.zero)
    "a zero byte immediately below the size boundary must remain present"
  assertTrue (zeroTailInput.byte? zeroTailInput.sizeWord == none)
    "the exact size boundary must be absent"
  assertTrue (emptyInput.byte? (word 0) == none)
    "empty input must have no byte at offset zero"
  assertTrue (representativeInput.byte? (word 0) == some (word 0x12))
    "the first input byte must widen exactly to a Core Word"
  assertTrue (representativeInput.byte? (word 2) == some (word 0xab))
    "a middle input byte must be selected by its exact natural offset"
  assertTrue (representativeInput.byte? (word 3) == some (word 0xff))
    "the final input byte must remain addressable"
  assertTrue (representativeInput.byte? (word 4) == none)
    "the offset immediately after the final byte must be absent"
  assertTrue (representativeInput.byte? Word.maximum == none)
    "the maximum Core Word offset must be absent"
  assertTrue (representativeInput.byte? beyondMachineIndex == none)
    "input indexing must not narrow a large natural offset to machine width"
  assertTrue
    ((representativeInput.byte? (word 3)).isSome ==
      decide ((word 3).val < representativeInput.sizeWord.val))
    "the final byte must agree with the exact observed size"
  assertTrue
    ((representativeInput.byte? (word 4)).isSome ==
      decide ((word 4).val < representativeInput.sizeWord.val))
    "the first absent byte must agree with the exact observed size"
  assertTrue
    ((representativeInput.byte? Word.maximum).isSome ==
      decide (Word.maximum.val < representativeInput.sizeWord.val))
    "the maximum Word boundary must agree with the exact observed size"
  let presentZero := representativeInput.byte? (word 1)
  assertTrue (presentZero == some Word.zero)
    "a present zero byte must produce some zero"
  assertTrue (presentZero != none)
    "a present zero byte must remain distinct from an absent byte"
  assertTrue (emptyInput.wordBE? (word 0) == none)
    "empty input must not contain a complete Word window"
  assertTrue (singletonInput.wordBE? (word 0) == none)
    "a one-byte input must not be padded into a Word"
  assertTrue (shortWordInput.wordBE? (word 0) == none)
    "a 31-byte input must not be padded into a Word"
  assertTrue (exactWordInput.wordBE? (word 0) == some sequentialWord0)
    "an exact 32-byte input must decode as the known big-endian Word"
  assertTrue (slidingWordInput.wordBE? (word 0) == some sequentialWord0)
    "the first complete window must decode exactly"
  assertTrue (slidingWordInput.wordBE? (word 1) == some sequentialWord1)
    "a middle complete window must decode exactly"
  assertTrue (slidingWordInput.wordBE? (word 2) == some sequentialWord2)
    "the final complete window must decode exactly"
  assertTrue (slidingWordInput.wordBE? (word 3) == none)
    "the partial window immediately after the final complete one must fail"
  assertTrue (slidingWordInput.wordBE? Word.maximum == none)
    "the maximum Core Word offset must fail without wrapping"
  assertTrue (slidingWordInput.wordBE? beyondMachineIndex == none)
    "large exact natural offsets must not narrow to machine width"
  assertTrue (zeroWordInput.wordBE? (word 0) == some Word.zero)
    "32 zero bytes must remain present as some zero"
  assertTrue (zeroWordInput.wordBE? (word 0) != none)
    "a zero Word must remain distinct from an absent window"
  assertTrue
    (slidingWordInput.bytes.extract 1 33 == encodeWordBytesBE sequentialWord1)
    "encoding a loaded Word must recover its exact selected window"
  assertTrue (allWordBytesCoherent slidingWordInput (word 1) sequentialWord1)
    "all 32 selected bytes must agree with big-endian Word.byteAt"
  match representativeInput.byte? (word 3) with
  | none =>
      throw (IO.userError "the final representative byte unexpectedly disappeared")
  | some result =>
      assertTrue (decide (result.val < 256))
        "every successfully observed byte must remain below 256"

end Tests
end

section
-- leanmerge: from Solcore.Test.RuntimeScalars
/-! Executable boundary tests for canonical runtime scalar encodings. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core
open Solcore.ContractRuntime

private def bytes (values : List UInt8) : ByteArray :=
  values.toByteArray

private def repeated (count : Nat) (digit : Char) : String :=
  String.ofList (List.replicate count digit)

private def acceptedCanonical {α : Type}
    (decode : String → Option α) (encode : α → String) (text : String) : Bool :=
  match decode text with
  | some value => encode value == text
  | none => false

private def addressMaximum : Address :=
  ⟨addressModulus - 1, by decide⟩

private def testBytesText : IO Unit := do
  let empty := bytes []
  let zero := bytes [0]
  let maximum := bytes [0xff]
  let multiple := bytes [0x12, 0x34, 0xab]
  let padded := bytes [0, 0x12, 0]
  let cases := [empty, zero, maximum, multiple, padded]
  assertTrue (encodeBytesText empty == "0x")
    "empty bytes must encode as the prefix alone"
  assertTrue
    (encodeBytesText zero == "0x00" &&
      encodeBytesText maximum == "0xff")
    "byte endpoint encodings must use two lowercase digits"
  assertTrue (encodeBytesText multiple == "0x1234ab")
    "multiple bytes must retain their order in hexadecimal text"
  assertTrue (encodeBytesText padded == "0x001200")
    "byte text must retain leading and trailing zero octets"
  assertTrue
    (cases.all fun value => decodeBytesText? (encodeBytesText value) == some value)
    "canonical byte text must round-trip every representative value"
  assertTrue
    (acceptedCanonical decodeBytesText? encodeBytesText "0x0012ff00")
    "accepted byte text must re-encode to its identical canonical spelling"
  let rejected := ["00", "0X00", "0xFF", "0x0g", "0x0"]
  assertTrue (rejected.all fun text => (decodeBytesText? text).isNone)
    "byte text must reject missing or altered prefixes, uppercase, non-hex, and odd width"

private def testAddressText : IO Unit := do
  let zero : Address := ⟨0, by decide⟩
  let one : Address := ⟨1, by decide⟩
  let values := [zero, one, addressMaximum]
  let zeros := repeated 40 '0'
  let maximum := repeated 40 'f'
  assertTrue (encodeAddressText zero == "0x" ++ zeros)
    "zero address must encode as exactly forty zero digits"
  assertTrue (encodeAddressText one == "0x" ++ repeated 39 '0' ++ "1")
    "address one must be left-padded to forty digits"
  assertTrue (encodeAddressText addressMaximum == "0x" ++ maximum)
    "maximum address must encode as forty lowercase f digits"
  assertTrue
    (values.all fun value => decodeAddressText? (encodeAddressText value) == some value)
    "canonical address text must round-trip endpoint values"
  assertTrue
    (acceptedCanonical decodeAddressText? encodeAddressText
      ("0x" ++ repeated 38 '0' ++ "12"))
    "accepted address text must re-encode to its identical canonical spelling"
  let wrongWidths := ["0x" ++ repeated 39 '0', "0x" ++ repeated 41 '0']
  assertTrue (wrongWidths.all fun text => (decodeAddressText? text).isNone)
    "address text must reject both thirty-nine and forty-one digits"
  let malformed := [
    zeros,
    "0X" ++ zeros,
    "0x" ++ repeated 39 '0' ++ "F",
    "0x" ++ repeated 39 '0' ++ "g"
  ]
  assertTrue (malformed.all fun text => (decodeAddressText? text).isNone)
    "address text must reject missing or altered prefixes, uppercase, and non-hex digits"

private def testWordText : IO Unit := do
  let zero := Word.zero
  let one := word 1
  let values := [zero, one, Word.maximum]
  let zeros := repeated 64 '0'
  let maximum := repeated 64 'f'
  assertTrue (encodeWordText zero == "0x" ++ zeros)
    "zero word must encode as exactly sixty-four zero digits"
  assertTrue (encodeWordText one == "0x" ++ repeated 63 '0' ++ "1")
    "word one must be left-padded to sixty-four digits"
  assertTrue (encodeWordText Word.maximum == "0x" ++ maximum)
    "maximum word must encode as sixty-four lowercase f digits"
  assertTrue
    (values.all fun value => decodeWordText? (encodeWordText value) == some value)
    "canonical word text must round-trip endpoint values"
  assertTrue
    (acceptedCanonical decodeWordText? encodeWordText
      ("0x" ++ repeated 62 '0' ++ "12"))
    "accepted word text must re-encode to its identical canonical spelling"
  let wrongWidths := ["0x" ++ repeated 63 '0', "0x" ++ repeated 65 '0']
  assertTrue (wrongWidths.all fun text => (decodeWordText? text).isNone)
    "word text must reject both sixty-three and sixty-five digits"
  let malformed := [
    zeros,
    "0X" ++ zeros,
    "0x" ++ repeated 63 '0' ++ "F",
    "0x" ++ repeated 63 '0' ++ "g"
  ]
  assertTrue (malformed.all fun text => (decodeWordText? text).isNone)
    "word text must reject missing or altered prefixes, uppercase, and non-hex digits"

private def testWordBytesBE : IO Unit := do
  let marker := word (0xaa * 2 ^ 248 + 0x1122)
  let encoded := encodeWordBytesBE marker
  let expected := bytes ([0xaa] ++ List.replicate 29 0 ++ [0x11, 0x22])
  assertTrue (encoded.size == 32)
    "big-endian word encoding must contain exactly thirty-two bytes"
  assertTrue (encoded == expected)
    "big-endian word encoding must match the complete independent byte fixture"
  assertTrue
    (encoded.data[0]? == some (0xaa : UInt8) &&
      encoded.data[30]? == some (0x11 : UInt8) &&
      encoded.data[31]? == some (0x22 : UInt8))
    "big-endian word encoding must place the most significant and final bytes correctly"
  assertTrue
    (encoded.data[0]?.map (fun byte => word byte.toNat) == some ((word 0).byteAt marker) &&
      encoded.data[30]?.map (fun byte => word byte.toNat) == some ((word 30).byteAt marker) &&
      encoded.data[31]?.map (fun byte => word byte.toNat) == some ((word 31).byteAt marker))
    "big-endian byte positions must agree directly with executable word byte selection"
  assertTrue
    (match decodeWordBytesBE? expected with
    | some value => encodeWordBytesBE value == expected
    | none => false)
    "accepted big-endian bytes must re-encode to their identical canonical sequence"
  let values := [Word.zero, word 1, marker, Word.maximum]
  assertTrue
    (values.all fun value =>
      decodeWordBytesBE? (encodeWordBytesBE value) == some value)
    "big-endian word bytes must round-trip representative values"
  let wrongWidths := [
    bytes (List.replicate 31 0),
    bytes (List.replicate 33 0)
  ]
  assertTrue (wrongWidths.all fun value => (decodeWordBytesBE? value).isNone)
    "big-endian word decoding must reject both thirty-one and thirty-three bytes"

def testRuntimeScalars : IO Unit := do
  testBytesText
  testAddressText
  testWordText
  testWordBytesBE

end Tests
end

section
-- leanmerge: from Solcore.Test.TransactionHostStorageHandler
/-! Focused executable checks for transaction-aware log handling. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core
open Solcore.ContractRuntime

private def address (value : Nat) : Address :=
  ⟨value % addressModulus, Nat.mod_lt _ (by decide)⟩

private def storageAddress_variant : Address := address 17
private def callerAddress_variant : Address := address 19
private def activeAddress : Address := address 23
private def account : Account := Account.empty
private def world : WorldState :=
  WorldState.empty.putAccount storageAddress_variant account

private def earlier : CheckedCoreWordLog := {
  emitter := address 29
  topic := word 31
  payload := word 37
}

private def created : Address := address 41

private def initialJournal : TransactionJournal :=
  (TransactionJournal.empty.recordLog earlier).recordCreatedContract created

private def effects : FrameEffectJournal TransactionJournal Unit :=
  ⟨initialJournal, ()⟩

private def context : TransactionHostStorageDriver.Context :=
  ⟨⟨storageAddress_variant,
      ⟨⟨world, effects⟩, (world, effects)⟩⟩,
    account,
    by rfl⟩

private def topic : Word := word 43
private def payload : Word := word 47

private def inputs : HostStorageDriver.ExecutionInputs := {
  codeAddress := activeAddress
  callValue := word 53
  callerAddress := callerAddress_variant
  inputData := HostStorageDriver.InputData.ofWord payload
  currentAddress := activeAddress
}

private def firstHandled :
    TransactionHostStorageDriver.Context × Unit :=
  TransactionHostStorageDriver.handleRequest inputs context
    (.emitLogWord topic payload)

private def secondHandled :
    TransactionHostStorageDriver.Context × Unit :=
  TransactionHostStorageDriver.handleRequest inputs firstHandled.1
    (.emitLogWord topic payload)

private def expected : CheckedCoreWordLog := {
  emitter := activeAddress
  topic := topic
  payload := payload
}

private def exactJournal : Bool :=
  secondHandled.1.workingJournal.logList == [earlier, expected, expected] &&
    secondHandled.1.workingJournal.createdContractList == [created]

private theorem compileTimeExactJournal : exactJournal = true := by
  native_decide

private theorem compileTimeWorldPreserved :
    firstHandled.1.context.values.working.1 = world := by
  simp [firstHandled, context]

private theorem compileTimeAccountPreserved :
    firstHandled.1.storageAccount = account := by
  simp [firstHandled, context]

private theorem compileTimeSelectorPreserved :
    firstHandled.1.context.storageAddress = storageAddress_variant := by
  simp [firstHandled, context]

private theorem compileTimeCheckpointPreserved :
    firstHandled.1.context.values.checkpoint = context.context.values.checkpoint := by
  simp [firstHandled]

def testTransactionHostStorageHandler : IO Unit := do
  assertTrue exactJournal
    "transaction log handling must append exact duplicate logs in order"

end Tests
end

section
-- leanmerge: from Solcore.Test.TransactionJournal
/-! Executable tests for ordered rollback-scoped transaction observations. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core
open Solcore.ContractRuntime

private def firstLog : CheckedCoreWordLog := {
  emitter := address 17
  topic := word 23
  payload := word 29
}

private def secondLog : CheckedCoreWordLog := {
  emitter := address 31
  topic := word 37
  payload := word 41
}

def testTransactionJournal : IO Unit := do
  let empty := TransactionJournal.empty
  assertTrue
    (empty.logList.isEmpty && empty.createdContractList.isEmpty)
    "an empty transaction journal must expose no logs or creations"

  let withDuplicateLogs :=
    (empty.recordLog firstLog).recordLog firstLog
  assertTrue
    (withDuplicateLogs.logList == [firstLog, firstLog])
    "log recording must preserve chronological order and duplicates"
  assertTrue
    withDuplicateLogs.createdContractList.isEmpty
    "log recording must not add a creation observation"

  let firstCreated := address 43
  let secondCreated := address 47
  let withFirstCreation :=
    withDuplicateLogs.recordCreatedContract firstCreated
  let completed :=
    (withFirstCreation.recordLog secondLog).recordCreatedContract secondCreated
  assertTrue
    (completed.logList == [firstLog, firstLog, secondLog])
    "creation recording must leave the ordered log trace unchanged"
  assertTrue
    (completed.createdContractList == [firstCreated, secondCreated])
    "successful creations must be observed in completion order"
  assertTrue
    (completed.logList[0]? == some {
      emitter := address 17
      topic := word 23
      payload := word 29
    })
    "a recorded log must retain its exact emitter, topic, and payload"

end Tests
end
