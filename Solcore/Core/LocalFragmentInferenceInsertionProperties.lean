import Solcore.Core.LocalFragmentTypingInsertionProperties

/-! Executable type inference is unchanged by positional insertion for the
independent local fragment. Equality includes rejection as well as success. -/

set_option autoImplicit false

namespace Solcore.Core

theorem Expr.LocalFragment.infer_insert
    {expr : Expr} (fragment : expr.LocalFragment)
    (leading suffix : Context) (inserted : Ty)
    (definitions : DataEnvironment := []) :
    infer? (leading ++ inserted :: suffix) (expr.weakenAt leading.length) definitions =
      infer? (leading ++ suffix) expr definitions := by
  cases original : infer? (leading ++ suffix) expr definitions with
  | some type =>
      exact infer_complete
        ((fragment.hasType_insert_iff leading suffix inserted).mpr (infer_sound original))
  | none =>
      cases shifted :
          infer? (leading ++ inserted :: suffix) (expr.weakenAt leading.length) definitions with
      | none => rfl
      | some type =>
          have originalTyping :=
            (fragment.hasType_insert_iff leading suffix inserted).mp (infer_sound shifted)
          have originalSome := infer_complete originalTyping
          rw [original] at originalSome
          cases originalSome

theorem Expr.LocalFragment.infer_weaken_zero
    {expr : Expr} (fragment : expr.LocalFragment)
    (context : Context) (inserted : Ty) (definitions : DataEnvironment := []) :
    infer? (inserted :: context) (expr.weakenAt 0) definitions =
      infer? context expr definitions :=
  fragment.infer_insert [] context inserted definitions

end Solcore.Core
