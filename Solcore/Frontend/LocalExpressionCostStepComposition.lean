import Solcore.Core.Correspondence

/-! Exact continuation-local paths for the primitive forms used by the
canonical cost bridge. These lemmas count transitions without executing a runner. -/

set_option autoImplicit false

namespace Solcore.Frontend.CostStepComposition

open Core

theorem unary {environment : Environment} {initialStore finalStore : Store}
    {op : UnaryOp} {operand : Expr} {operandValue result : Value}
    {continuation : List Frame} {childCost : Nat}
    (child : Steps childCost
      ⟨.eval operand environment, .unaryApply op :: continuation, initialStore⟩
      ⟨.ret operandValue, .unaryApply op :: continuation, finalStore⟩)
    (applied : op.apply operandValue = some result) :
    Steps (childCost + 2)
      ⟨.eval (.unary op operand) environment, continuation, initialStore⟩
      ⟨.ret result, continuation, finalStore⟩ := by
  have path := Steps.cons .enterUnary (child.trans (.cons (.applyUnary applied) .refl))
  simpa only [Nat.add_assoc] using path

theorem binary {environment : Environment} {initialStore middleStore finalStore : Store}
    {op : BinaryOp} {left right : Expr} {leftValue rightValue result : Value}
    {continuation : List Frame} {leftCost rightCost : Nat}
    (leftPath : Steps leftCost
      ⟨.eval left environment, .binaryRight op right environment :: continuation, initialStore⟩
      ⟨.ret leftValue, .binaryRight op right environment :: continuation, middleStore⟩)
    (rightPath : Steps rightCost
      ⟨.eval right environment, .binaryApply op leftValue :: continuation, middleStore⟩
      ⟨.ret rightValue, .binaryApply op leftValue :: continuation, finalStore⟩)
    (applied : op.apply leftValue rightValue = some result) :
    Steps (leftCost + rightCost + 3)
      ⟨.eval (.binary op left right) environment, continuation, initialStore⟩
      ⟨.ret result, continuation, finalStore⟩ := by
  have path := Steps.cons .enterBinary
    (leftPath.trans (.cons .enterBinaryRight (rightPath.trans (.cons (.applyBinary applied) .refl))))
  simpa only [Nat.add_assoc] using path

theorem ifTrue {environment : Environment} {initialStore middleStore finalStore : Store}
    {condition thenBranch elseBranch : Expr} {result : Value}
    {continuation : List Frame} {conditionCost branchCost : Nat}
    (conditionPath : Steps conditionCost
      ⟨.eval condition environment, .ifBranches thenBranch elseBranch environment :: continuation, initialStore⟩
      ⟨.ret (.bool true), .ifBranches thenBranch elseBranch environment :: continuation, middleStore⟩)
    (branchPath : Steps branchCost
      ⟨.eval thenBranch environment, continuation, middleStore⟩
      ⟨.ret result, continuation, finalStore⟩) :
    Steps (conditionCost + branchCost + 2)
      ⟨.eval (.ifE condition thenBranch elseBranch) environment, continuation, initialStore⟩
      ⟨.ret result, continuation, finalStore⟩ := by
  have path := Steps.cons .enterIf (conditionPath.trans (.cons .chooseTrue branchPath))
  simpa only [Nat.add_assoc] using path

theorem ifFalse {environment : Environment} {initialStore middleStore finalStore : Store}
    {condition thenBranch elseBranch : Expr} {result : Value}
    {continuation : List Frame} {conditionCost branchCost : Nat}
    (conditionPath : Steps conditionCost
      ⟨.eval condition environment, .ifBranches thenBranch elseBranch environment :: continuation, initialStore⟩
      ⟨.ret (.bool false), .ifBranches thenBranch elseBranch environment :: continuation, middleStore⟩)
    (branchPath : Steps branchCost
      ⟨.eval elseBranch environment, continuation, middleStore⟩
      ⟨.ret result, continuation, finalStore⟩) :
    Steps (conditionCost + branchCost + 2)
      ⟨.eval (.ifE condition thenBranch elseBranch) environment, continuation, initialStore⟩
      ⟨.ret result, continuation, finalStore⟩ := by
  have path := Steps.cons .enterIf (conditionPath.trans (.cons .chooseFalse branchPath))
  simpa only [Nat.add_assoc] using path

end Solcore.Frontend.CostStepComposition
