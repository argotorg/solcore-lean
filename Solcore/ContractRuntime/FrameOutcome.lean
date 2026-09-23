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

/-!
## Consolidated module: `Solcore.ContractRuntime.FrameOutcomeProperties`
-/

/-! Focused laws for syntax-independent contract frame halt outcomes. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime
namespace FrameOutcome

universe u

@[simp] theorem kind_returned
    {TrapReason : Type u} (data : Bytes) :
    kind (FrameOutcome.returned (TrapReason := TrapReason) data) =
      FrameHaltKind.returned := by
  rfl

@[simp] theorem kind_reverted
    {TrapReason : Type u} (data : Bytes) :
    kind (FrameOutcome.reverted (TrapReason := TrapReason) data) =
      FrameHaltKind.reverted := by
  rfl

@[simp] theorem kind_trapped
    {TrapReason : Type u} (reason : TrapReason) :
    kind (FrameOutcome.trapped reason) = FrameHaltKind.trapped := by
  rfl

theorem returndata?_eq_some_iff
    {TrapReason : Type u} (outcome : FrameOutcome TrapReason) (data : Bytes) :
    returndata? outcome = some data ↔
      outcome = FrameOutcome.returned data := by
  cases outcome <;> constructor <;> intro h <;> cases h <;> rfl

theorem revertdata?_eq_some_iff
    {TrapReason : Type u} (outcome : FrameOutcome TrapReason) (data : Bytes) :
    revertdata? outcome = some data ↔
      outcome = FrameOutcome.reverted data := by
  cases outcome <;> constructor <;> intro h <;> cases h <;> rfl

theorem trapReason?_eq_some_iff
    {TrapReason : Type u} (outcome : FrameOutcome TrapReason)
    (reason : TrapReason) :
    trapReason? outcome = some reason ↔
      outcome = FrameOutcome.trapped reason := by
  cases outcome <;> constructor <;> intro h <;> cases h <;> rfl

end FrameOutcome
end Solcore.ContractRuntime

/-!
## Consolidated module: `Solcore.ContractRuntime.FrameOutcomeTrapReasonMap`
-/

/-! Caller-supplied pure mapping of frame trap-reason types. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.FrameOutcome

universe u v

/-- Preserve halt kind and byte payload while mapping only trapped reasons. -/
def mapTrapReason
    {TrapReason : Type u} {MappedTrapReason : Type v}
    (mapReason : TrapReason → MappedTrapReason)
    (outcome : FrameOutcome TrapReason) :
    FrameOutcome MappedTrapReason :=
  match outcome with
  | .returned data => .returned data
  | .reverted data => .reverted data
  | .trapped reason => .trapped (mapReason reason)

end Solcore.ContractRuntime.FrameOutcome

/-!
## Consolidated module: `Solcore.ContractRuntime.FrameOutcomeTrapReasonMapProperties`
-/

/-! Constructor and composition laws for frame trap-reason mapping. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.FrameOutcome

universe u v w

@[simp] theorem mapTrapReason_returned
    {TrapReason : Type u} {MappedTrapReason : Type v}
    (mapReason : TrapReason → MappedTrapReason) (data : Bytes) :
    mapTrapReason mapReason
        (FrameOutcome.returned (TrapReason := TrapReason) data) =
      FrameOutcome.returned (TrapReason := MappedTrapReason) data := by
  rfl

@[simp] theorem mapTrapReason_reverted
    {TrapReason : Type u} {MappedTrapReason : Type v}
    (mapReason : TrapReason → MappedTrapReason) (data : Bytes) :
    mapTrapReason mapReason
        (FrameOutcome.reverted (TrapReason := TrapReason) data) =
      FrameOutcome.reverted (TrapReason := MappedTrapReason) data := by
  rfl

@[simp] theorem mapTrapReason_trapped
    {TrapReason : Type u} {MappedTrapReason : Type v}
    (mapReason : TrapReason → MappedTrapReason)
    (reason : TrapReason) :
    mapTrapReason mapReason (FrameOutcome.trapped reason) =
      FrameOutcome.trapped (mapReason reason) := by
  rfl

@[simp] theorem mapTrapReason_id
    {TrapReason : Type u} (outcome : FrameOutcome TrapReason) :
    mapTrapReason (fun reason => reason) outcome = outcome := by
  cases outcome <;> rfl

@[simp] theorem mapTrapReason_comp
    {TrapReason : Type u}
    {IntermediateTrapReason : Type v}
    {MappedTrapReason : Type w}
    (first : TrapReason → IntermediateTrapReason)
    (second : IntermediateTrapReason → MappedTrapReason)
    (outcome : FrameOutcome TrapReason) :
    mapTrapReason second (mapTrapReason first outcome) =
      mapTrapReason (fun reason => second (first reason)) outcome := by
  cases outcome <;> rfl

end Solcore.ContractRuntime.FrameOutcome
