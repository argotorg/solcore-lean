import Solcore.Frontend.ComputationBodyFragment
import Solcore.Core.Eval
import Solcore.Core.LocalFragment

/-! Literal child insertion lifts through the whole body. Actual bound values
extend the retained prefix; no typing or closure reconstruction is required. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem ComputationBodyFragment.evaluates_insert_iff {F : Core.Expr → Prop}
    (childInsert : ∀ {expr}, F expr → ∀ (leading suffix : Core.Environment) (inserted : Core.Value),
      ∀ {initialStore finalStore value},
        Core.Evaluates (leading ++ inserted :: suffix) initialStore
          (expr.weakenAt leading.length) value finalStore ↔
          Core.Evaluates (leading ++ suffix) initialStore expr value finalStore)
    {expr : Core.Expr} (fragment : ComputationBodyFragment F expr)
    (leading suffix : Core.Environment) (inserted : Core.Value)
    {initialStore finalStore : Core.Store} {value : Core.Value} :
    Core.Evaluates (leading ++ inserted :: suffix) initialStore
      (expr.weakenAt leading.length) value finalStore ↔
      Core.Evaluates (leading ++ suffix) initialStore expr value finalStore := by
  induction fragment generalizing leading initialStore finalStore value with
  | wordTest =>
      exact (Core.Expr.LocalFragment.binary .var .word).evaluates_insert_iff leading suffix inserted
  | unit =>
      simp only [Core.Expr.weakenAt]
      constructor <;> intro evaluation <;> cases evaluation <;> exact .unit
  | leaf child => exact childInsert child leading suffix inserted
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
