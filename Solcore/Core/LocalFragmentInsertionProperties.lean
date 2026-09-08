import Solcore.Core.LocalFragment
import Solcore.Core.Eval

/-! Exact insertion for the local syntax fragment, independent of Resolved
typing and lowering. Retained prefixes let the proof pass under nested lets;
the arbitrary inserted value is never substituted for an original reference. -/

set_option autoImplicit false

namespace Solcore.Core

private theorem lookup_insert (leading suffix : Environment) (inserted : Value) (index : Nat) :
    (leading ++ inserted :: suffix)[if leading.length ≤ index then index + 1 else index]? =
      (leading ++ suffix)[index]? := by
  induction leading generalizing index with
  | nil => simp
  | cons head leading ih =>
      cases index with
      | zero => simp
      | succ index =>
          by_cases shifted : leading.length ≤ index <;>
            simpa [shifted, Nat.succ_le_succ_iff] using ih index

/-- Positional insertion preserves and reflects successful evaluation literally.
No typing, original scoping, freshness, allocation or store-passivity is assumed. -/
theorem Expr.LocalFragment.evaluates_insert_iff
    {expr : Expr} (fragment : expr.LocalFragment)
    (leading suffix : Environment) (inserted : Value)
    {initialStore finalStore : Store} {value : Value} :
    Evaluates (leading ++ inserted :: suffix) initialStore
      (expr.weakenAt leading.length) value finalStore ↔
      Evaluates (leading ++ suffix) initialStore expr value finalStore := by
  induction fragment generalizing leading initialStore finalStore value with
  | unit =>
      simp only [Expr.weakenAt]
      constructor <;> intro evaluation <;> cases evaluation <;> exact .unit
  | bool =>
      simp only [Expr.weakenAt]
      constructor <;> intro evaluation <;> cases evaluation <;> exact .bool
  | word =>
      simp only [Expr.weakenAt]
      constructor <;> intro evaluation <;> cases evaluation <;> exact .word
  | @var index =>
      simp only [Expr.weakenAt]
      have positions := lookup_insert leading suffix inserted index
      by_cases shifted : leading.length ≤ index <;>
        simp only [shifted, ↓reduceIte] at positions ⊢
      all_goals
        constructor
        · intro evaluation
          cases evaluation with
          | var found => exact .var (positions.symm.trans found)
        · intro evaluation
          cases evaluation with
          | var found => exact .var (positions.trans found)
  | pair _ _ leftIH rightIH =>
      simp only [Expr.weakenAt]
      constructor
      · intro evaluation
        cases evaluation with
        | pair left right => exact .pair ((leftIH leading).mp left) ((rightIH leading).mp right)
      · intro evaluation
        cases evaluation with
        | pair left right => exact .pair ((leftIH leading).mpr left) ((rightIH leading).mpr right)
  | unary _ ih =>
      simp only [Expr.weakenAt]
      constructor
      · intro evaluation
        cases evaluation with
        | unary child applied => exact .unary ((ih leading).mp child) applied
      · intro evaluation
        cases evaluation with
        | unary child applied => exact .unary ((ih leading).mpr child) applied
  | binary _ _ leftIH rightIH =>
      simp only [Expr.weakenAt]
      constructor
      · intro evaluation
        cases evaluation with
        | binary left right applied =>
            exact .binary ((leftIH leading).mp left) ((rightIH leading).mp right) applied
      · intro evaluation
        cases evaluation with
        | binary left right applied =>
            exact .binary ((leftIH leading).mpr left) ((rightIH leading).mpr right) applied
  | letE _ _ valueIH bodyIH =>
      simp only [Expr.weakenAt]
      constructor
      · intro evaluation
        cases evaluation with
        | @letE _ _ _ _ _ _ boundValue _ valueEvaluation bodyEvaluation =>
            exact .letE ((valueIH leading).mp valueEvaluation)
              ((bodyIH (boundValue :: leading)).mp bodyEvaluation)
      · intro evaluation
        cases evaluation with
        | @letE _ _ _ _ _ _ boundValue _ valueEvaluation bodyEvaluation =>
            exact .letE ((valueIH leading).mpr valueEvaluation)
              ((bodyIH (boundValue :: leading)).mpr bodyEvaluation)
  | ifE _ _ _ conditionIH thenIH elseIH =>
      simp only [Expr.weakenAt]
      constructor
      · intro evaluation
        cases evaluation with
        | ifTrue condition branch =>
            exact .ifTrue ((conditionIH leading).mp condition) ((thenIH leading).mp branch)
        | ifFalse condition branch =>
            exact .ifFalse ((conditionIH leading).mp condition) ((elseIH leading).mp branch)
      · intro evaluation
        cases evaluation with
        | ifTrue condition branch =>
            exact .ifTrue ((conditionIH leading).mpr condition) ((thenIH leading).mpr branch)
        | ifFalse condition branch =>
            exact .ifFalse ((conditionIH leading).mpr condition) ((elseIH leading).mpr branch)

theorem Expr.LocalFragment.evaluates_weaken_zero_iff
    {expr : Expr} (fragment : expr.LocalFragment) (environment : Environment) (inserted : Value)
    {initialStore finalStore : Store} {value : Value} :
    Evaluates (inserted :: environment) initialStore (expr.weakenAt 0) value finalStore ↔
      Evaluates environment initialStore expr value finalStore :=
  fragment.evaluates_insert_iff [] environment inserted

theorem Evaluates.weakenAt_zero_localFragment
    {expr : Expr} {environment : Environment} {initialStore finalStore : Store} {value : Value}
    (evaluation : Evaluates environment initialStore expr value finalStore)
    (fragment : expr.LocalFragment) (inserted : Value) :
    Evaluates (inserted :: environment) initialStore (expr.weakenAt 0) value finalStore :=
  (fragment.evaluates_weaken_zero_iff environment inserted).mpr evaluation

theorem Evaluates.reflect_weakenAt_zero_localFragment
    {expr : Expr} {environment : Environment} {inserted : Value}
    {initialStore finalStore : Store} {value : Value}
    (evaluation : Evaluates (inserted :: environment) initialStore
      (expr.weakenAt 0) value finalStore)
    (fragment : expr.LocalFragment) :
    Evaluates environment initialStore expr value finalStore :=
  (fragment.evaluates_weaken_zero_iff environment inserted).mp evaluation

end Solcore.Core
