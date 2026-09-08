import Solcore.Core.LocalFragment
import Solcore.Core.Typing

/-! Exact typing insertion for the independent local Core fragment. The
retained prefix fixes the insertion position and extends beneath each let.
Neither the inserted type nor the context needs a runtime inhabitant or a
well-formedness assumption. Data definitions are retained unchanged. -/

set_option autoImplicit false

namespace Solcore.Core

private theorem lookup_insert (leading suffix : Context) (inserted : Ty) (index : Nat) :
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

/-- Positional insertion preserves and reflects the exact assigned type.
No original-scoping or runtime-environment premise is needed. -/
theorem Expr.LocalFragment.hasType_insert_iff
    {expr : Expr} (fragment : expr.LocalFragment)
    (leading suffix : Context) (inserted : Ty)
    {type : Ty} {definitions : DataEnvironment} :
    HasType (leading ++ inserted :: suffix) (expr.weakenAt leading.length) type definitions ↔
      HasType (leading ++ suffix) expr type definitions := by
  induction fragment generalizing leading type with
  | unit =>
      simp only [Expr.weakenAt]
      constructor <;> intro typing <;> cases typing <;> exact .unit
  | bool =>
      simp only [Expr.weakenAt]
      constructor <;> intro typing <;> cases typing <;> exact .bool
  | word =>
      simp only [Expr.weakenAt]
      constructor <;> intro typing <;> cases typing <;> exact .word
  | @var index =>
      simp only [Expr.weakenAt]
      have positions := lookup_insert leading suffix inserted index
      by_cases shifted : leading.length ≤ index <;>
        simp only [shifted, ↓reduceIte] at positions ⊢
      all_goals
        constructor
        · intro typing
          cases typing with
          | var found => exact .var (positions.symm.trans found)
        · intro typing
          cases typing with
          | var found => exact .var (positions.trans found)
  | unary _ ih =>
      simp only [Expr.weakenAt]
      constructor
      · intro typing
        cases typing with
        | unary child => exact .unary ((ih leading).mp child)
      · intro typing
        cases typing with
        | unary child => exact .unary ((ih leading).mpr child)
  | binary _ _ leftIH rightIH =>
      simp only [Expr.weakenAt]
      constructor
      · intro typing
        cases typing with
        | binary left right => exact .binary ((leftIH leading).mp left) ((rightIH leading).mp right)
      · intro typing
        cases typing with
        | binary left right => exact .binary ((leftIH leading).mpr left) ((rightIH leading).mpr right)
  | letE _ _ valueIH bodyIH =>
      simp only [Expr.weakenAt]
      constructor
      · intro typing
        cases typing with
        | @letE _ _ _ _ boundType _ valueTyping bodyTyping =>
            exact .letE ((valueIH leading).mp valueTyping)
              ((bodyIH (boundType :: leading)).mp bodyTyping)
      · intro typing
        cases typing with
        | @letE _ _ _ _ boundType _ valueTyping bodyTyping =>
            exact .letE ((valueIH leading).mpr valueTyping)
              ((bodyIH (boundType :: leading)).mpr bodyTyping)
  | ifE _ _ _ conditionIH thenIH elseIH =>
      simp only [Expr.weakenAt]
      constructor
      · intro typing
        cases typing with
        | ifE condition thenBranch elseBranch =>
            exact .ifE ((conditionIH leading).mp condition)
              ((thenIH leading).mp thenBranch) ((elseIH leading).mp elseBranch)
      · intro typing
        cases typing with
        | ifE condition thenBranch elseBranch =>
            exact .ifE ((conditionIH leading).mpr condition)
              ((thenIH leading).mpr thenBranch) ((elseIH leading).mpr elseBranch)

theorem Expr.LocalFragment.hasType_weaken_zero_iff
    {expr : Expr} (fragment : expr.LocalFragment) (context : Context) (inserted : Ty)
    {type : Ty} {definitions : DataEnvironment} :
    HasType (inserted :: context) (expr.weakenAt 0) type definitions ↔
      HasType context expr type definitions :=
  fragment.hasType_insert_iff [] context inserted

theorem HasType.weakenAt_zero_localFragment
    {context : Context} {expr : Expr} {type : Ty} {definitions : DataEnvironment}
    (typing : HasType context expr type definitions)
    (fragment : expr.LocalFragment) (inserted : Ty) :
    HasType (inserted :: context) (expr.weakenAt 0) type definitions :=
  (fragment.hasType_weaken_zero_iff context inserted).mpr typing

theorem HasType.reflect_weakenAt_zero_localFragment
    {context : Context} {expr : Expr} {inserted type : Ty} {definitions : DataEnvironment}
    (typing : HasType (inserted :: context) (expr.weakenAt 0) type definitions)
    (fragment : expr.LocalFragment) :
    HasType context expr type definitions :=
  (fragment.hasType_weaken_zero_iff context inserted).mp typing

end Solcore.Core
