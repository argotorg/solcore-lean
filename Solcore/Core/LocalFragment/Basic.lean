import Solcore.Core.Eval
import Solcore.Core.Primitive
import Solcore.Core.Typing

/-!
# Basic local Core fragment

Syntax, evaluation, typing, and inference under positional insertion. These
properties are independent of derived comparisons and runtime store safety.
-/

set_option autoImplicit false

/-!
## Syntax fragment
-/

/-! A syntax-only boundary for the local expression fragment. It neither
requires typing or valid indices nor asserts that an expression evaluates.
All children are checked, including branches that execution may not select.
Variables may return arbitrary runtime values, but no form creates or calls
a closure or reads or writes a cell. -/


namespace Solcore.Core

inductive Expr.LocalFragment : Expr → Prop where
  | unit : LocalFragment .unit
  | bool {value : Bool} : LocalFragment (.bool value)
  | word {value : Word} : LocalFragment (.word value)
  | var {index : Nat} : LocalFragment (.var index)
  | pair {left right : Expr} :
      LocalFragment left → LocalFragment right → LocalFragment (.pair left right)
  | unary {op : UnaryOp} {operand : Expr} :
      LocalFragment operand → LocalFragment (.unary op operand)
  | binary {op : BinaryOp} {left right : Expr} :
      LocalFragment left → LocalFragment right → LocalFragment (.binary op left right)
  | letE {value body : Expr} :
      LocalFragment value → LocalFragment body → LocalFragment (.letE value body)
  | ifE {condition thenBranch elseBranch : Expr} :
      LocalFragment condition → LocalFragment thenBranch → LocalFragment elseBranch →
      LocalFragment (.ifE condition thenBranch elseBranch)

/-- Positional insertion stays within the fragment at every cutoff, including
under lets. This structural fact imposes no bound on the inserted position. -/
theorem Expr.LocalFragment.weakenAt {expr : Expr}
    (fragment : Expr.LocalFragment expr) (cutoff : Nat) :
    Expr.LocalFragment (expr.weakenAt cutoff) := by
  induction fragment generalizing cutoff with
  | unit => simp only [Expr.weakenAt]; exact .unit
  | bool => simp only [Expr.weakenAt]; exact .bool
  | word => simp only [Expr.weakenAt]; exact .word
  | var =>
      simp only [Expr.weakenAt]
      split <;> exact .var
  | pair _ _ leftIH rightIH =>
      simp only [Expr.weakenAt]
      exact .pair (leftIH cutoff) (rightIH cutoff)
  | unary _ ih => simp only [Expr.weakenAt]; exact .unary (ih cutoff)
  | binary _ _ leftIH rightIH =>
      simp only [Expr.weakenAt]
      exact .binary (leftIH cutoff) (rightIH cutoff)
  | letE _ _ valueIH bodyIH =>
      simp only [Expr.weakenAt]
      exact .letE (valueIH cutoff) (bodyIH (cutoff + 1))
  | ifE _ _ _ conditionIH thenIH elseIH =>
      simp only [Expr.weakenAt]
      exact .ifE (conditionIH cutoff) (thenIH cutoff) (elseIH cutoff)

end Solcore.Core

/-!
## Evaluation under inserted environments
-/

/-! Exact insertion for the local syntax fragment, independent of Resolved
typing and lowering. Retained prefixes let the proof pass under nested lets;
the arbitrary inserted value is never substituted for an original reference. -/


namespace Solcore.Core

private theorem lookup_environment_insert (leading suffix : Environment) (inserted : Value) (index : Nat) :
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
      have positions := lookup_environment_insert leading suffix inserted index
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

/-!
## Typing under inserted contexts
-/

/-! Exact typing insertion for the independent local Core fragment. The
retained prefix fixes the insertion position and extends beneath each let.
Neither the inserted type nor the context needs a runtime inhabitant or a
well-formedness assumption. Data definitions are retained unchanged. -/


namespace Solcore.Core

private theorem lookup_context_insert (leading suffix : Context) (inserted : Ty) (index : Nat) :
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
      have positions := lookup_context_insert leading suffix inserted index
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
  | pair _ _ leftIH rightIH =>
      simp only [Expr.weakenAt]
      constructor
      · intro typing
        cases typing with
        | pair left right => exact .pair ((leftIH leading).mp left) ((rightIH leading).mp right)
      · intro typing
        cases typing with
        | pair left right => exact .pair ((leftIH leading).mpr left) ((rightIH leading).mpr right)
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

/-!
## Inference under inserted contexts
-/

/-! Executable type inference is unchanged by positional insertion for the
independent local fragment. Equality includes rejection as well as success. -/


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

