import Solcore.Oracle.V5.ProbeValidation
import Solcore.Semantics.CheckedCoreContract

/-! Safe construction of the Oracle v5 top-level invocation boundary. -/

set_option autoImplicit false

namespace Solcore.Oracle.V5

open Solcore.Semantics

/-- The exact semantic invocation paired with its order-preserving probe set. -/
structure PreparedInvocation where
  invocation : TopLevelInvocation
  probes : ProbeValidation.ValidatedProbes

namespace InvocationPreparation

/--
Prepare bytes only after typed preflight established the declared calldata
limit. `Limits.Valid` then proves that the semantic Word-sized length is safe.
-/
def prepare
    (limits : Limits)
    (limitsValid : limits.Valid)
    (input : InvocationInput)
    (withinLimit : input.calldata.size ≤ limits.calldataBytes) :
    Except DuplicateProbe PreparedInvocation := do
  let probes ← ProbeValidation.validate input.probes
  let size_lt_wordModulus : input.calldata.size < Solcore.Core.wordModulus :=
    Nat.lt_of_le_of_lt withinLimit limitsValid
  .ok {
    invocation := {
      target := input.target
      caller := input.caller
      callValue := input.callValue
      inputData := {
        bytes := input.calldata
        size_lt_wordModulus
      }
    }
    probes
  }

end InvocationPreparation

end Solcore.Oracle.V5
