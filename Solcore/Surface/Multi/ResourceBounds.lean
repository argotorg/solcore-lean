import Solcore.Surface.Multi.Grammar
import Solcore.Surface.Multi.Measure

set_option autoImplicit false

namespace Solcore.Surface.Multi

/-- The fixed fast-parser work bound for `terminalCount`, where the count
already includes the logical EOF terminal. -/
def parseBound (terminalCount : Nat) : Nat :=
  let boundaryCount := terminalCount + 1
  1 + 32 * Grammar.F * boundaryCount +
    256 * Grammar.F * boundaryCount * boundaryCount

@[simp] theorem parseBound_equation (terminalCount : Nat) :
    parseBound terminalCount =
      1 + 32 * Grammar.F * (terminalCount + 1) +
        256 * Grammar.F * (terminalCount + 1) * (terminalCount + 1) :=
  rfl

/-- The fixed structural-validation work bound for the concrete AST carrier
count measured by `astNodeMeasure`. -/
def structureBound (nodeCount : Nat) : Nat :=
  32 * (nodeCount + 1) * (nodeCount + 1)

@[simp] theorem structureBound_equation (nodeCount : Nat) :
    structureBound nodeCount = 32 * (nodeCount + 1) * (nodeCount + 1) :=
  rfl

theorem parseBound_positive (terminalCount : Nat) :
    0 < parseBound terminalCount := by
  simp only [parseBound]
  omega

theorem structureBound_positive (nodeCount : Nat) :
    0 < structureBound nodeCount := by
  simp [structureBound]

theorem parseBound_monotone {left right : Nat} (less : left ≤ right) :
    parseBound left ≤ parseBound right := by
  simp only [parseBound]
  have boundaryLess : left + 1 ≤ right + 1 :=
    Nat.add_le_add_right less 1
  apply Nat.add_le_add
  · exact Nat.add_le_add_left
      (Nat.mul_le_mul_left (32 * Grammar.F) boundaryLess) 1
  · exact Nat.mul_le_mul
      (Nat.mul_le_mul_left (256 * Grammar.F) boundaryLess)
      boundaryLess

theorem structureBound_monotone {left right : Nat} (less : left ≤ right) :
    structureBound left ≤ structureBound right := by
  simp only [structureBound]
  have nodeLess : left + 1 ≤ right + 1 :=
    Nat.add_le_add_right less 1
  exact Nat.mul_le_mul (Nat.mul_le_mul_left 32 nodeLess) nodeLess

end Solcore.Surface.Multi
