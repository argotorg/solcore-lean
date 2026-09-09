import Solcore.Core.LocalFragment

/-! Recursive applications of pure callers. Membership does not constrain an
actual returned closure's body or captures, and creates no new closure. -/

set_option autoImplicit false

namespace Solcore.Frontend

inductive RecursiveLocalComputationFragment : Core.Expr → Prop where
  | pure {expr : Core.Expr} (child : expr.LocalFragment) : RecursiveLocalComputationFragment expr
  | application {function argument : Core.Expr}
      (callee : RecursiveLocalComputationFragment function)
      (operand : RecursiveLocalComputationFragment argument) :
      RecursiveLocalComputationFragment (.apply function argument)

end Solcore.Frontend
