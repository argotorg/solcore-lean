import Solcore.Syntax.Parser.TermRecursiveProperties

/-! Unconditional parser shapes for ordinary mutual-fuel soundness proofs. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.TermInternals

/-- Trivial statement validity is closed under one recursive statement layer. -/
theorem ordinaryShapeStatementClosure :
    RecursiveStatementClosure (fun _ _ => True) := {
  close := by
    intro _ _ _
    trivial
}

/-- The mutual recursive parser contract with syntax validity erased. -/
theorem coreTermFuel_ordinaryShape_contract (fuel : Nat) :
    RecursiveFuelContract (fun _ _ => True) fuel :=
  coreRecursiveWithFuel_contract (fun _ _ => True)
    ordinaryShapeStatementClosure fuel

/-- Every fuel-bounded Core expression preserves its token window. -/
theorem coreExpressionWithFuel_ordinary_preservesTokenWindow (fuel : Nat) :
    Parser.PreservesTokenWindow (coreExpressionWithFuel fuel) :=
  (coreTermFuel_ordinaryShape_contract fuel).expression.preservesTokenWindow

/-- Every successful fuel-bounded Core expression strictly advances. -/
theorem coreExpressionWithFuel_ordinary_cursor_lt_onSuccess (fuel : Nat)
    {input output : State} {value : Expr}
    (result : coreExpressionWithFuel fuel input = .ok value output) :
    input.cursor < output.cursor :=
  (coreTermFuel_ordinaryShape_contract fuel).expression.cursorLtOnSuccess
    result

/-- Every fuel-bounded Core pattern preserves its token window. -/
theorem corePatternWithFuel_ordinary_preservesTokenWindow (fuel : Nat) :
    Parser.PreservesTokenWindow (corePatternWithFuel fuel) :=
  (coreTermFuel_ordinaryShape_contract fuel).pattern.preservesTokenWindow

/-- Every fuel-bounded Core statement preserves its token window. -/
theorem coreStatementWithFuel_ordinary_preservesTokenWindow (fuel : Nat) :
    Parser.PreservesTokenWindow (coreStatementWithFuel fuel) :=
  (coreTermFuel_ordinaryShape_contract fuel).statement.preservesTokenWindow

end Solcore.Syntax.Parser.TermInternals
