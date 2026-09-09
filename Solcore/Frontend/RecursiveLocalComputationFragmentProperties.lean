import Solcore.Frontend.RecursiveLocalComputationFragment
import Solcore.Frontend.RecursiveLocalComputation
import Solcore.Resolved.LocalFragmentProperties

/-! Recursive caller membership follows original elaboration and is stable
under positional weakening, without inspecting actual closure bodies. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem RecursiveLocalComputationFragment.weakenAt {expr : Core.Expr}
    (fragment : RecursiveLocalComputationFragment expr) (cutoff : Nat) :
    RecursiveLocalComputationFragment (expr.weakenAt cutoff) := by
  induction fragment with
  | pure child => exact .pure (child.weakenAt cutoff)
  | application _ _ calleeIH operandIH =>
      simp only [Core.Expr.weakenAt]
      exact .application calleeIH operandIH
  | binary _ _ leftIH rightIH =>
      simp only [Core.Expr.weakenAt]
      exact .binary leftIH rightIH

theorem RecursiveLocalComputationElaborates.core_fragment
    {table : LocalNameTable} {context : Resolved.Context} {source : Syntax.Expr}
    {core : Core.Expr} {type : Core.Ty}
    (elaboration : RecursiveLocalComputationElaborates table context source core type) :
    RecursiveLocalComputationFragment core := by
  induction elaboration with
  | pure _ lowered _ => exact .pure lowered.localFragment
  | group _ ih => exact ih
  | application _ _ calleeIH operandIH => exact .application calleeIH operandIH
  | binary _ _ _ leftIH rightIH => exact .binary leftIH rightIH

end Solcore.Frontend
