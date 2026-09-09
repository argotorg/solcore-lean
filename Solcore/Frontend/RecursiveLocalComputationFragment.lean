import Solcore.Core.LocalFragment

/-! Recursive applications, unary/strict binaries, pairs and conditionals/lets of pure callers.
Membership does not constrain actual returned closure bodies or captures;
the caller syntax itself has no lambda constructor. -/

set_option autoImplicit false

namespace Solcore.Frontend

inductive RecursiveLocalComputationFragment : Core.Expr → Prop where
  | pure {expr : Core.Expr} (child : expr.LocalFragment) : RecursiveLocalComputationFragment expr
  | application {function argument : Core.Expr}
      (callee : RecursiveLocalComputationFragment function)
      (operand : RecursiveLocalComputationFragment argument) :
      RecursiveLocalComputationFragment (.apply function argument)

  | pair {left right : Core.Expr}
      (leftChild : RecursiveLocalComputationFragment left)
      (rightChild : RecursiveLocalComputationFragment right) :
      RecursiveLocalComputationFragment (.pair left right)

  | binary {op : Core.BinaryOp} {left right : Core.Expr}
      (leftChild : RecursiveLocalComputationFragment left)
      (rightChild : RecursiveLocalComputationFragment right) :
      RecursiveLocalComputationFragment (.binary op left right)

  | ifE {condition thenBranch elseBranch : Core.Expr}
      (conditionChild : RecursiveLocalComputationFragment condition)
      (thenChild : RecursiveLocalComputationFragment thenBranch)
      (elseChild : RecursiveLocalComputationFragment elseBranch) :
      RecursiveLocalComputationFragment (.ifE condition thenBranch elseBranch)

  | unary {op : Core.UnaryOp} {operand : Core.Expr}
      (child : RecursiveLocalComputationFragment operand) :
      RecursiveLocalComputationFragment (.unary op operand)

  | letE {initializer body : Core.Expr}
      (initializerChild : RecursiveLocalComputationFragment initializer)
      (bodyChild : RecursiveLocalComputationFragment body) :
      RecursiveLocalComputationFragment (.letE initializer body)

end Solcore.Frontend
