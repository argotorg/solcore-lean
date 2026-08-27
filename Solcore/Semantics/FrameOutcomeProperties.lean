import Solcore.Semantics.FrameOutcome

/-! Focused laws for syntax-independent contract frame halt outcomes. -/

set_option autoImplicit false

namespace Solcore.Semantics
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
end Solcore.Semantics
