import Solcore.ContractRuntime.HostDriver

/-! Additional fuel for exhausted or unsupported handled host execution. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime

universe u

namespace HostDriverResult

/--
Resume exhaustion by executing its retained state. An unsupported request stays
suspended while its offered fuel grows. Completed and faulted results stay exact.
-/
def resumeWithFuel
    {Context : Type u}
    (result : HostDriverResult Context)
    (handler : HostHandler Context)
    (additional : Nat) : HostDriverResult Context :=
  match result with
  | ⟨context, .outOfFuel exhausted⟩ =>
      HostDriver.run handler context additional exhausted
  | ⟨context, .unsupported suspension remainingFuel⟩ =>
      ⟨context, .unsupported suspension (remainingFuel + additional)⟩
  | terminal => terminal

@[simp] theorem resumeWithFuel_outOfFuel
    {Context : Type u}
    (context : Context)
    (state : Core.State)
    (handler : HostHandler Context)
    (additional : Nat) :
    resumeWithFuel ⟨context, .outOfFuel state⟩ handler additional =
      HostDriver.run handler context additional state := by
  rfl

@[simp] theorem resumeWithFuel_done
    {Context : Type u}
    (context : Context)
    (value : Core.Value)
    (store : Core.Store)
    (handler : HostHandler Context)
    (additional : Nat) :
    resumeWithFuel ⟨context, .done value store⟩ handler additional =
      ⟨context, .done value store⟩ := by
  rfl

@[simp] theorem resumeWithFuel_fault
    {Context : Type u}
    (context : Context)
    (error : Core.MachineFault)
    (state : Core.State)
    (handler : HostHandler Context)
    (additional : Nat) :
    resumeWithFuel ⟨context, .fault error state⟩ handler additional =
      ⟨context, .fault error state⟩ := by
  rfl

@[simp] theorem resumeWithFuel_unsupported
    {Context : Type u}
    (context : Context)
    (suspension : Core.HostSuspension)
    (remainingFuel : Nat)
    (handler : HostHandler Context)
    (additional : Nat) :
    resumeWithFuel ⟨context, .unsupported suspension remainingFuel⟩
        handler additional =
      ⟨context, .unsupported suspension (remainingFuel + additional)⟩ := by
  rfl

end HostDriverResult

end Solcore.ContractRuntime
