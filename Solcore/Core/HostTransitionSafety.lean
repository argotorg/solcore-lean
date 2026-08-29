import Solcore.Core.HostCoreTransitionSafety
import Solcore.Core.HostMachineProperties

/-! Type preservation at the executable Core/host boundary. -/

set_option autoImplicit false

namespace Solcore.Core

theorem hostTransition_preserves_state_type
    {definitions : DataEnvironment}
    {state next : State} {resultType : Ty}
    (stateTyping : HostStateHasType state resultType definitions)
    (transition : HostTransition state next) :
    HostStateHasType next resultType definitions := by
  cases transition with
  | core step =>
      exact transition_preserves_host_state_type stateTyping step
  | beginApplication =>
      cases stateTyping with
      | ret store functionTyping continuationTyping =>
          cases continuationTyping with
          | cons frameTyping restTyping =>
              cases frameTyping with
              | applyArgument environmentTyping argumentTyping =>
                  cases functionTyping with
                  | hostFunction =>
                      exact .eval store environmentTyping argumentTyping
                        (.cons .hostApply restTyping)

theorem hostRequestEmission_hasType
    {definitions : DataEnvironment}
    {state : State} {suspension : HostSuspension} {resultType : Ty}
    (stateTyping : HostStateHasType state resultType definitions)
    (emission : HostRequestEmission state suspension) :
    HostSuspensionHasType suspension resultType definitions := by
  cases emission with
  | storageRead =>
      cases stateTyping with
      | ret store valueTyping continuationTyping =>
          cases continuationTyping with
          | cons frameTyping restTyping =>
              cases frameTyping with
              | hostApply =>
                  cases valueTyping with
                  | word => exact .intro store restTyping
  | storageWrite =>
      cases stateTyping with
      | ret store valueTyping continuationTyping =>
          cases continuationTyping with
          | cons frameTyping restTyping =>
              cases frameTyping with
              | hostApply =>
                  cases valueTyping with
                  | pair leftTyping rightTyping =>
                      cases leftTyping
                      cases rightTyping
                      exact .intro store restTyping
  | storageAddress =>
      cases stateTyping with
      | ret store valueTyping continuationTyping =>
          cases continuationTyping with
          | cons frameTyping restTyping =>
              cases frameTyping with
              | hostApply =>
                  cases valueTyping
                  exact .intro store restTyping
  | codeAddress =>
      cases stateTyping with
      | ret store valueTyping continuationTyping =>
          cases continuationTyping with
          | cons frameTyping restTyping =>
              cases frameTyping with
              | hostApply =>
                  cases valueTyping
                  exact .intro store restTyping
  | callValue =>
      cases stateTyping with
      | ret store valueTyping continuationTyping =>
          cases continuationTyping with
          | cons frameTyping restTyping =>
              cases frameTyping with
              | hostApply =>
                  cases valueTyping
                  exact .intro store restTyping
  | callerAddress =>
      cases stateTyping with
      | ret store valueTyping continuationTyping =>
          cases continuationTyping with
          | cons frameTyping restTyping =>
              cases frameTyping with
              | hostApply =>
                  cases valueTyping
                  exact .intro store restTyping

theorem hostAdvance_next_preserves_state_type
    {definitions : DataEnvironment}
    {state next : State} {resultType : Ty}
    (stateTyping : HostStateHasType state resultType definitions)
    (advanced : hostAdvance state = .next next) :
    HostStateHasType next resultType definitions :=
  hostTransition_preserves_state_type stateTyping (hostAdvance_next_iff.mp advanced)

theorem hostAdvance_suspended_hasType
    {definitions : DataEnvironment}
    {state : State} {suspension : HostSuspension} {resultType : Ty}
    (stateTyping : HostStateHasType state resultType definitions)
    (advanced : hostAdvance state = .suspended suspension) :
    HostSuspensionHasType suspension resultType definitions :=
  hostRequestEmission_hasType stateTyping (hostAdvance_suspended_iff.mp advanced)

end Solcore.Core
