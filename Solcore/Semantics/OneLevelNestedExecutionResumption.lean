import Solcore.Semantics.OneLevelNestedExecution

/-! Resumption for bounded one-level nested checked-Core execution. -/

set_option autoImplicit false

namespace Solcore.Semantics.OneLevelNestedExecution

/--
Keep a terminal result stable, or continue its exact retained scheduler mode
with one additional shared-fuel budget.
-/
def resumeWithFuel
    {initialWorld : WorldState}
    {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    (result : Result initialWorld rootContract rootInvocation)
    (additional : Nat) :
    Result initialWorld rootContract rootInvocation :=
  match result.view with
  | .completed _terminal => result
  | .outOfFuel registry mode reachable =>
      runMode registry additional mode reachable

end Solcore.Semantics.OneLevelNestedExecution
