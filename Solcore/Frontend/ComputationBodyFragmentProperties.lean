import Solcore.Frontend.ComputationBodyFragment
import Solcore.Core.RenamingSyntax

/-! Whole-tail weakening needs only weakening of the supplied child predicate.
The retained prefix gains one slot underneath each actual Core let binder. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem ComputationBodyFragment.weakenAt {F : Core.Expr → Prop}
    (childWeakens : ∀ {expr}, F expr → ∀ cutoff, F (expr.weakenAt cutoff))
    {expr : Core.Expr} (fragment : ComputationBodyFragment F expr) (cutoff : Nat) :
    ComputationBodyFragment F (expr.weakenAt cutoff) := by
  induction fragment generalizing cutoff with
  | unit => simpa only [Core.Expr.weakenAt] using (ComputationBodyFragment.unit (F := F))
  | wordTest =>
      simp only [Core.Expr.weakenAt]
      split <;> exact .wordTest
  | leaf child => exact .leaf (childWeakens child cutoff)
  | letE _ _ headIH tailIH =>
      simp only [Core.Expr.weakenAt]
      exact .letE (headIH cutoff) (tailIH (cutoff + 1))
  | ifE _ _ _ guardIH yesIH noIH =>
      simp only [Core.Expr.weakenAt]
      exact .ifE (guardIH cutoff) (yesIH cutoff) (noIH cutoff)

end Solcore.Frontend
