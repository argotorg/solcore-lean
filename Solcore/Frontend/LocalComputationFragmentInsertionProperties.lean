import Solcore.Frontend.LocalComputationFragment
import Solcore.Core.LocalFragment

/-! Caller insertion preserves literal successful results and both stores.
Actual invoked bodies and captures are unchanged, not assumed pure or typed. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem LocalComputationFragment.evaluates_insert_iff
    {expr : Core.Expr} (fragment : LocalComputationFragment expr)
    (leading suffix : Core.Environment) (inserted : Core.Value)
    {initialStore finalStore : Core.Store} {value : Core.Value} :
    Core.Evaluates (leading ++ inserted :: suffix) initialStore
      (expr.weakenAt leading.length) value finalStore ↔
      Core.Evaluates (leading ++ suffix) initialStore expr value finalStore := by
  induction fragment generalizing leading initialStore finalStore value with
  | pure child => exact child.evaluates_insert_iff leading suffix inserted
  | application callee operand =>
      simp only [Core.Expr.weakenAt]
      constructor
      · intro evaluation
        cases evaluation with
        | apply functionEvaluation argumentEvaluation bodyEvaluation =>
            exact .apply ((callee.evaluates_insert_iff leading suffix inserted).mp functionEvaluation)
              ((operand.evaluates_insert_iff leading suffix inserted).mp argumentEvaluation) bodyEvaluation
      · intro evaluation
        cases evaluation with
        | apply functionEvaluation argumentEvaluation bodyEvaluation =>
            exact .apply ((callee.evaluates_insert_iff leading suffix inserted).mpr functionEvaluation)
              ((operand.evaluates_insert_iff leading suffix inserted).mpr argumentEvaluation) bodyEvaluation
  | letE _ _ headIH tailIH =>
      simp only [Core.Expr.weakenAt]
      constructor
      · intro evaluation
        cases evaluation with
        | @letE _ _ _ _ _ _ boundValue _ head tail =>
            exact .letE ((headIH leading).mp head) ((tailIH (boundValue :: leading)).mp tail)
      · intro evaluation
        cases evaluation with
        | @letE _ _ _ _ _ _ boundValue _ head tail =>
            exact .letE ((headIH leading).mpr head) ((tailIH (boundValue :: leading)).mpr tail)
  | ifE _ _ _ guardIH yesIH noIH =>
      simp only [Core.Expr.weakenAt]
      constructor
      · intro evaluation
        cases evaluation with
        | ifTrue condition branch => exact .ifTrue ((guardIH leading).mp condition) ((yesIH leading).mp branch)
        | ifFalse condition branch => exact .ifFalse ((guardIH leading).mp condition) ((noIH leading).mp branch)
      · intro evaluation
        cases evaluation with
        | ifTrue condition branch => exact .ifTrue ((guardIH leading).mpr condition) ((yesIH leading).mpr branch)
        | ifFalse condition branch => exact .ifFalse ((guardIH leading).mpr condition) ((noIH leading).mpr branch)

end Solcore.Frontend
