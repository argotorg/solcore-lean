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
  induction fragment generalizing cutoff with
  | pure child => exact .pure (child.weakenAt cutoff)
  | application _ _ calleeIH operandIH =>
      simp only [Core.Expr.weakenAt]
      exact .application (calleeIH cutoff) (operandIH cutoff)
  | binary _ _ leftIH rightIH =>
      simp only [Core.Expr.weakenAt]
      exact .binary (leftIH cutoff) (rightIH cutoff)
  | ifE _ _ _ conditionIH thenIH elseIH =>
      simp only [Core.Expr.weakenAt]
      exact .ifE (conditionIH cutoff) (thenIH cutoff) (elseIH cutoff)
  | unary _ childIH =>
      simp only [Core.Expr.weakenAt]
      exact .unary (childIH cutoff)
  | letE _ _ initializerIH bodyIH =>
      simp only [Core.Expr.weakenAt]
      exact .letE (initializerIH cutoff) (bodyIH (cutoff + 1))

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
  | conditional _ _ _ conditionIH thenIH elseIH => exact .ifE conditionIH thenIH elseIH
  | logicalNot _ childIH => exact .unary childIH
  | bitNot _ childIH => exact .unary childIH
  | logicalAnd _ _ leftIH rightIH => exact .ifE leftIH rightIH (.pure .bool)
  | logicalOr _ _ leftIH rightIH => exact .ifE leftIH (.pure .bool) rightIH
  | notEqual _ _ leftIH rightIH => exact .unary (.binary leftIH rightIH)
  | lessEqual _ _ leftIH rightIH => exact .unary (.binary leftIH rightIH)
  | less _ _ leftIH rightIH =>
      exact .letE leftIH (.letE (rightIH.weakenAt 0) (.pure (.binary .var .var)))
  | greaterEqual _ _ leftIH rightIH =>
      exact .unary (.letE leftIH (.letE (rightIH.weakenAt 0) (.pure (.binary .var .var))))

end Solcore.Frontend
