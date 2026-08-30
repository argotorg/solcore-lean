import Solcore.Oracle.V5.Input

/-! Typed collection and scalar measurements before Oracle v5 admission. -/

set_option autoImplicit false

namespace Solcore.Oracle.V5.TypedPreflight

def check (request : Request) : Option PreflightExhaustion :=
  if exceeded : request.limits.scenarioEntries < request.query.scenarioEntries then
    some {
      resource := .scenarioEntries
      limit := request.limits.scenarioEntries
      consumed := request.query.scenarioEntries
      exceeded
    }
  else if exceeded : request.limits.identifierBytes < request.maxIdentifierBytes then
    some {
      resource := .identifierBytes
      limit := request.limits.identifierBytes
      consumed := request.maxIdentifierBytes
      exceeded
    }
  else if exceeded : request.limits.calldataBytes < request.query.calldataBytes then
    some {
      resource := .calldataBytes
      limit := request.limits.calldataBytes
      consumed := request.query.calldataBytes
      exceeded
    }
  else
    none

theorem check_eq_none_iff (request : Request) :
    check request = none ↔
      request.query.scenarioEntries ≤ request.limits.scenarioEntries ∧
      request.maxIdentifierBytes ≤ request.limits.identifierBytes ∧
      request.query.calldataBytes ≤ request.limits.calldataBytes := by
  by_cases scenarioExceeded :
      request.limits.scenarioEntries < request.query.scenarioEntries
  · have scenarioNotWithin :
        ¬ request.query.scenarioEntries ≤ request.limits.scenarioEntries :=
      Nat.not_le_of_gt scenarioExceeded
    simp [check, scenarioExceeded, scenarioNotWithin]
  · have scenarioWithin :
        request.query.scenarioEntries ≤ request.limits.scenarioEntries :=
      Nat.le_of_not_gt scenarioExceeded
    by_cases identifierExceeded :
        request.limits.identifierBytes < request.maxIdentifierBytes
    · have identifierNotWithin :
          ¬ request.maxIdentifierBytes ≤ request.limits.identifierBytes :=
        Nat.not_le_of_gt identifierExceeded
      simp [check, scenarioExceeded, scenarioWithin,
        identifierExceeded, identifierNotWithin]
    · have identifierWithin :
          request.maxIdentifierBytes ≤ request.limits.identifierBytes :=
        Nat.le_of_not_gt identifierExceeded
      by_cases calldataExceeded :
          request.limits.calldataBytes < request.query.calldataBytes
      · have calldataNotWithin :
            ¬ request.query.calldataBytes ≤ request.limits.calldataBytes :=
          Nat.not_le_of_gt calldataExceeded
        simp [check, scenarioExceeded, scenarioWithin,
          identifierExceeded, identifierWithin,
          calldataExceeded, calldataNotWithin]
      · have calldataWithin :
            request.query.calldataBytes ≤ request.limits.calldataBytes :=
          Nat.le_of_not_gt calldataExceeded
        simp [check, scenarioExceeded, scenarioWithin,
          identifierExceeded, identifierWithin,
          calldataExceeded, calldataWithin]

theorem scenarioEntries_within_of_check_eq_none
    {request : Request}
    (accepted : check request = none) :
    request.query.scenarioEntries ≤ request.limits.scenarioEntries :=
  (check_eq_none_iff request).mp accepted |>.1

theorem identifierBytes_within_of_check_eq_none
    {request : Request}
    (accepted : check request = none) :
    request.maxIdentifierBytes ≤ request.limits.identifierBytes :=
  (check_eq_none_iff request).mp accepted |>.2.1

theorem calldataBytes_within_of_check_eq_none
    {request : Request}
    (accepted : check request = none) :
    request.query.calldataBytes ≤ request.limits.calldataBytes :=
  (check_eq_none_iff request).mp accepted |>.2.2

theorem check_scenarioEntries_exceeded
    (request : Request)
    (exceeded : request.limits.scenarioEntries < request.query.scenarioEntries) :
    check request = some {
      resource := .scenarioEntries
      limit := request.limits.scenarioEntries
      consumed := request.query.scenarioEntries
      exceeded
    } := by
  simp [check, exceeded]

theorem check_identifierBytes_exceeded
    (request : Request)
    (scenarioWithin :
      request.query.scenarioEntries ≤ request.limits.scenarioEntries)
    (exceeded : request.limits.identifierBytes < request.maxIdentifierBytes) :
    check request = some {
      resource := .identifierBytes
      limit := request.limits.identifierBytes
      consumed := request.maxIdentifierBytes
      exceeded
    } := by
  simp [check, Nat.not_lt.mpr scenarioWithin, exceeded]

theorem check_calldataBytes_exceeded
    (request : Request)
    (scenarioWithin :
      request.query.scenarioEntries ≤ request.limits.scenarioEntries)
    (identifierWithin :
      request.maxIdentifierBytes ≤ request.limits.identifierBytes)
    (exceeded : request.limits.calldataBytes < request.query.calldataBytes) :
    check request = some {
      resource := .calldataBytes
      limit := request.limits.calldataBytes
      consumed := request.query.calldataBytes
      exceeded
    } := by
  simp [check, Nat.not_lt.mpr scenarioWithin,
    Nat.not_lt.mpr identifierWithin, exceeded]

theorem check_failure_resource
    {request : Request}
    {exhaustion : PreflightExhaustion}
    (failed : check request = some exhaustion) :
    exhaustion.resource = .scenarioEntries ∨
      exhaustion.resource = .identifierBytes ∨
      exhaustion.resource = .calldataBytes := by
  unfold check at failed
  split at failed
  · left
    exact congrArg PreflightExhaustion.resource (Option.some.inj failed).symm
  · split at failed
    · right
      left
      exact congrArg PreflightExhaustion.resource (Option.some.inj failed).symm
    · split at failed
      · right
        right
        exact congrArg PreflightExhaustion.resource (Option.some.inj failed).symm
      · simp at failed

end Solcore.Oracle.V5.TypedPreflight
