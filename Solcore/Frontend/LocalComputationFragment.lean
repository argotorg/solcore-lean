import Solcore.Core.LocalFragment

/-! Caller syntax for mixed local computations. Unlike the old pure fragment,
this boundary admits applications, but not source closure construction. The
body and captures of an actual called closure are not restricted by membership. -/

set_option autoImplicit false

namespace Solcore.Frontend

inductive LocalComputationFragment : Core.Expr → Prop where
  | pure {expr : Core.Expr} (child : expr.LocalFragment) : LocalComputationFragment expr
  | application {function argument : Core.Expr}
      (callee : function.LocalFragment) (operand : argument.LocalFragment) :
      LocalComputationFragment (.apply function argument)
  | letE {initializer body : Core.Expr}
      (head : LocalComputationFragment initializer) (tail : LocalComputationFragment body) :
      LocalComputationFragment (.letE initializer body)
  | ifE {condition thenBranch elseBranch : Core.Expr}
      (guard : LocalComputationFragment condition)
      (yes : LocalComputationFragment thenBranch) (no : LocalComputationFragment elseBranch) :
      LocalComputationFragment (.ifE condition thenBranch elseBranch)

end Solcore.Frontend
