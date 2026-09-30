import Solcore.Core.HostRunner

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
