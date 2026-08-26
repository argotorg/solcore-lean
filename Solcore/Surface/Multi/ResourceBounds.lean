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

end Solcore.Surface.Multi
