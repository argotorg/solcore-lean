import Solcore.Core.HostMachine

/-! Internal failure reasons for dispatching one checked contract-word call. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime

/-- Failures that occur before a child contract produces a terminal outcome. -/
inductive ContractCallFailure where
  | invalidAddress
  | unavailable
  | depthExceeded
  | insufficientBalance
  | balanceOverflow
  | nonceOverflow
  | addressCollision
  deriving Repr, BEq, DecidableEq

namespace ContractCallFailure

/-- Stable internal code injected into the typed call-failure response branch. -/
def code : ContractCallFailure → Core.Word
  | .invalidAddress => ⟨0, by decide⟩
  | .unavailable => ⟨1, by decide⟩
  | .depthExceeded => ⟨2, by decide⟩
  | .insufficientBalance => ⟨3, by decide⟩
  | .balanceOverflow => ⟨4, by decide⟩
  | .nonceOverflow => ⟨5, by decide⟩
  | .addressCollision => ⟨6, by decide⟩

/-- Convert a dispatch failure into the dedicated Core call-result branch. -/
def result (failure : ContractCallFailure) : Core.ContractCallWordResult :=
  .failed failure.code

end ContractCallFailure

end Solcore.ContractRuntime
