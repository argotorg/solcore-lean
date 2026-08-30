import Solcore.Semantics.OneLevelNestedValueCallProperties

/-! External compile consumers for nested value-call scheduler laws. -/

set_option autoImplicit false

namespace Tests.Adr0147NestedValueSchedulerExternalProperties

example :=
  Solcore.Semantics.OneLevelNestedExecution.CallProfile.request_legacy
example :=
  Solcore.Semantics.OneLevelNestedExecution.CallProfile.request_withValue
example :=
  Solcore.Semantics.OneLevelNestedExecution.CallProfile.target_legacy
example :=
  Solcore.Semantics.OneLevelNestedExecution.CallProfile.target_withValue
example :=
  Solcore.Semantics.OneLevelNestedExecution.CallProfile.invocation_legacy
example :=
  Solcore.Semantics.OneLevelNestedExecution.CallProfile.invocation_withValue

end Tests.Adr0147NestedValueSchedulerExternalProperties
