import Solcore.ContractRuntime.RuntimeScalars

/-! Internal, syntax-independent outcomes produced when one contract frame halts. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime

universe u

/-- The three ways in which execution of one contract frame can halt. -/
inductive FrameHaltKind where
  | returned
  | reverted
  | trapped
  deriving Repr, BEq, DecidableEq

/--
The result of halting one contract frame. Successful return data, revert data,
and a trap reason are kept in distinct constructors so invalid combinations
cannot be represented.
-/
inductive FrameOutcome (TrapReason : Type u) : Type u where
  | returned (returndata : Bytes)
  | reverted (revertdata : Bytes)
  | trapped (reason : TrapReason)
  deriving BEq, DecidableEq

namespace FrameOutcome

/-- Classify an outcome without inspecting its payload. -/
def kind {TrapReason : Type u} : FrameOutcome TrapReason → FrameHaltKind
  | .returned _ => .returned
  | .reverted _ => .reverted
  | .trapped _ => .trapped

/-- Return the successful return data, and `none` for other halt kinds. -/
def returndata? {TrapReason : Type u} : FrameOutcome TrapReason → Option Bytes
  | .returned data => some data
  | .reverted _
  | .trapped _ => none

/-- Return the revert data, and `none` for other halt kinds. -/
def revertdata? {TrapReason : Type u} : FrameOutcome TrapReason → Option Bytes
  | .reverted data => some data
  | .returned _
  | .trapped _ => none

/-- Return the trap reason, and `none` for returned or reverted outcomes. -/
def trapReason? {TrapReason : Type u} :
    FrameOutcome TrapReason → Option TrapReason
  | .trapped reason => some reason
  | .returned _
  | .reverted _ => none

end FrameOutcome

end Solcore.ContractRuntime
