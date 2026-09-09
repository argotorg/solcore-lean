import Solcore.Frontend.RecursiveLocalComputationFragment
import Solcore.Core.LocalFragmentInsertionProperties

/-! Inserting a caller slot preserves literal successful values and stores.
Recursive callees retain the same actual closure, captures and invoked body.
Each let retains its actual bound value ahead of the caller prefix. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem RecursiveLocalComputationFragment.evaluates_insert_iff
    {expr : Core.Expr} (fragment : RecursiveLocalComputationFragment expr)
    (leading suffix : Core.Environment) (inserted : Core.Value)
    {initialStore finalStore : Core.Store} {value : Core.Value} :
    Core.Evaluates (leading ++ inserted :: suffix) initialStore
      (expr.weakenAt leading.length) value finalStore ↔
      Core.Evaluates (leading ++ suffix) initialStore expr value finalStore := by
  induction fragment generalizing leading initialStore finalStore value with
  | pure child => exact child.evaluates_insert_iff leading suffix inserted
  | application _ _ calleeIH operandIH =>
      simp only [Core.Expr.weakenAt]
      constructor
      · intro evaluation
        cases evaluation with
        | apply functionEvaluation argumentEvaluation bodyEvaluation =>
            exact .apply ((calleeIH leading).mp functionEvaluation) ((operandIH leading).mp argumentEvaluation) bodyEvaluation
      · intro evaluation
        cases evaluation with
        | apply functionEvaluation argumentEvaluation bodyEvaluation =>
            exact .apply ((calleeIH leading).mpr functionEvaluation) ((operandIH leading).mpr argumentEvaluation) bodyEvaluation
  | binary _ _ leftIH rightIH =>
      simp only [Core.Expr.weakenAt]
      constructor
      · intro evaluation
        cases evaluation with
        | binary leftEvaluation rightEvaluation applied =>
            exact .binary ((leftIH leading).mp leftEvaluation) ((rightIH leading).mp rightEvaluation) applied
      · intro evaluation
        cases evaluation with
        | binary leftEvaluation rightEvaluation applied =>
            exact .binary ((leftIH leading).mpr leftEvaluation) ((rightIH leading).mpr rightEvaluation) applied
  | ifE _ _ _ conditionIH thenIH elseIH =>
      simp only [Core.Expr.weakenAt]
      constructor
      · intro evaluation
        cases evaluation with
        | ifTrue condition branch => exact .ifTrue ((conditionIH leading).mp condition) ((thenIH leading).mp branch)
        | ifFalse condition branch => exact .ifFalse ((conditionIH leading).mp condition) ((elseIH leading).mp branch)
      · intro evaluation
        cases evaluation with
        | ifTrue condition branch => exact .ifTrue ((conditionIH leading).mpr condition) ((thenIH leading).mpr branch)
        | ifFalse condition branch => exact .ifFalse ((conditionIH leading).mpr condition) ((elseIH leading).mpr branch)
  | unary _ childIH =>
      simp only [Core.Expr.weakenAt]
      constructor
      · intro evaluation
        cases evaluation with
        | unary child applied => exact .unary ((childIH leading).mp child) applied
      · intro evaluation
        cases evaluation with
        | unary child applied => exact .unary ((childIH leading).mpr child) applied
  | letE _ _ initializerIH bodyIH =>
      simp only [Core.Expr.weakenAt]
      constructor
      · intro evaluation
        cases evaluation with
        | @letE _ _ _ _ _ _ boundValue _ initializer body =>
            exact .letE ((initializerIH leading).mp initializer) ((bodyIH (boundValue :: leading)).mp body)
      · intro evaluation
        cases evaluation with
        | @letE _ _ _ _ _ _ boundValue _ initializer body =>
            exact .letE ((initializerIH leading).mpr initializer) ((bodyIH (boundValue :: leading)).mpr body)

end Solcore.Frontend
