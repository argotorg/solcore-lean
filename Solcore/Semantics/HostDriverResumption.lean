import Solcore.Semantics.HostDriver

/-! Resumption of exhausted handled host execution with additional fuel. -/

set_option autoImplicit false

namespace Solcore.Semantics

universe u

namespace HostDriverResult

/--
Resume only an exhausted result. Completed and faulted results remain exact.
-/
def resumeWithFuel
    {Context : Type u}
    (result : HostDriverResult Context)
    (handler : HostHandler Context)
    (additional : Nat) : HostDriverResult Context :=
  match result with
  | ⟨context, .outOfFuel exhausted⟩ =>
      HostDriver.run handler context additional exhausted
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

end HostDriverResult

end Solcore.Semantics
