import Solcore.Semantics.CheckedCreationPreflightFailureProperties

/-! External and executable checks for stable creation failure codes. -/

set_option autoImplicit false

namespace Tests.Adr0148CreationFailureBoundary

open Solcore.Core
open Solcore.Semantics

example := CheckedCreationPreflightFailure.unavailable_code
example := CheckedCreationPreflightFailure.nonceOverflow_code
example := CheckedCreationPreflightFailure.addressCollision_code
example := CheckedCreationPreflightFailure.transfer_code
example := CheckedCreationPreflightFailure.result_value
example := CheckedCreationPreflightFailure.result_response

private def codeOf
    (failure : CheckedCreationPreflightFailure) : Word :=
  failure.toContractCallFailure.code

private theorem exactCodes :
    codeOf .unavailable = ⟨1, by decide⟩ ∧
    codeOf (.transfer .insufficientBalance) = ⟨3, by decide⟩ ∧
    codeOf (.transfer .recipientOverflow) = ⟨4, by decide⟩ ∧
    codeOf .nonceOverflow = ⟨5, by decide⟩ ∧
    codeOf .addressCollision = ⟨6, by decide⟩ := by
  native_decide

def testAdr0148CreationFailureBoundary : IO Unit := do
  unless codeOf .unavailable == ⟨1, by decide⟩ do
    throw (IO.userError "creation unavailable code changed")
  unless codeOf (.transfer .insufficientBalance) == ⟨3, by decide⟩ do
    throw (IO.userError "creation balance failure compatibility changed")
  unless codeOf .nonceOverflow == ⟨5, by decide⟩ do
    throw (IO.userError "creation nonce-overflow code changed")
  unless codeOf .addressCollision == ⟨6, by decide⟩ do
    throw (IO.userError "creation collision code changed")

end Tests.Adr0148CreationFailureBoundary
