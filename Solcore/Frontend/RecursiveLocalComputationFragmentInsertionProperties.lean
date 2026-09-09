import Solcore.Frontend.RecursiveLocalComputationFragment
import Solcore.Core.LocalFragmentInsertionProperties

/-! Inserting a caller slot preserves literal successful values and stores.
Recursive callees retain the same actual closure, captures and invoked body. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem RecursiveLocalComputationFragment.evaluates_insert_iff
    {expr : Core.Expr} (fragment : RecursiveLocalComputationFragment expr)
    (leading suffix : Core.Environment) (inserted : Core.Value)
    {initialStore finalStore : Core.Store} {value : Core.Value} :
    Core.Evaluates (leading ++ inserted :: suffix) initialStore
      (expr.weakenAt leading.length) value finalStore ↔
      Core.Evaluates (leading ++ suffix) initialStore expr value finalStore := by
  induction fragment generalizing initialStore finalStore value with
  | pure child => exact child.evaluates_insert_iff leading suffix inserted
  | application _ _ calleeIH operandIH =>
      simp only [Core.Expr.weakenAt]
      constructor
      · intro evaluation
        cases evaluation with
        | apply functionEvaluation argumentEvaluation bodyEvaluation =>
            exact .apply (calleeIH.mp functionEvaluation) (operandIH.mp argumentEvaluation) bodyEvaluation
      · intro evaluation
        cases evaluation with
        | apply functionEvaluation argumentEvaluation bodyEvaluation =>
            exact .apply (calleeIH.mpr functionEvaluation) (operandIH.mpr argumentEvaluation) bodyEvaluation

end Solcore.Frontend
