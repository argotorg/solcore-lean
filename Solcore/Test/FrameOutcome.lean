import Solcore.ContractRuntime.FrameOutcome

/-! Executable boundary tests for internal contract-frame halt outcomes. -/

set_option autoImplicit false

namespace Tests

open Solcore.ContractRuntime

private inductive TestTrapReason where
  | invalidOperation
  | resourceLimit
  deriving BEq, DecidableEq

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def bytes (values : List UInt8) : ByteArray :=
  values.toByteArray

def testFrameOutcome : IO Unit := do
  let empty := bytes []
  let padded := bytes [0, 0x12, 0]
  let returnedEmpty : FrameOutcome TestTrapReason := .returned empty
  let returnedPadded : FrameOutcome TestTrapReason := .returned padded
  let revertedEmpty : FrameOutcome TestTrapReason := .reverted empty
  let revertedPadded : FrameOutcome TestTrapReason := .reverted padded
  let trappedInvalid : FrameOutcome TestTrapReason :=
    .trapped .invalidOperation
  let trappedLimit : FrameOutcome TestTrapReason :=
    .trapped .resourceLimit

  assertTrue
    (returnedEmpty.kind == .returned &&
      revertedEmpty.kind == .reverted &&
      trappedInvalid.kind == .trapped)
    "each frame outcome must report its own halt kind"
  assertTrue
    (returnedEmpty.returndata? == some empty &&
      returnedEmpty.returndata? != none)
    "an empty successful payload must remain some empty bytes, not absence"
  assertTrue
    (returnedEmpty.revertdata?.isNone && returnedEmpty.trapReason?.isNone)
    "a returned outcome must expose neither revert data nor a trap reason"
  assertTrue (returnedPadded.returndata? == some padded)
    "returned data must retain leading and trailing zero octets"
  assertTrue
    (revertedEmpty.revertdata? == some empty &&
      revertedEmpty.revertdata? != none)
    "an empty revert payload must remain some empty bytes, not absence"
  assertTrue
    (revertedEmpty.returndata?.isNone && revertedEmpty.trapReason?.isNone)
    "a reverted outcome must expose neither return data nor a trap reason"
  assertTrue (revertedPadded.revertdata? == some padded)
    "revert data must retain leading and trailing zero octets"
  assertTrue
    (trappedInvalid.trapReason? == some .invalidOperation &&
      trappedLimit.trapReason? == some .resourceLimit &&
      trappedInvalid != trappedLimit)
    "trap reasons must survive projection without merging distinct reasons"
  assertTrue
    (trappedInvalid.returndata?.isNone && trappedInvalid.revertdata?.isNone)
    "a trapped outcome must expose neither return data nor revert data"
  assertTrue
    (returnedEmpty != revertedEmpty &&
      returnedEmpty != trappedInvalid &&
      revertedEmpty != trappedInvalid)
    "returned, reverted, and trapped outcomes must remain distinct constructors"

end Tests
