import Solcore.Core.Correspondence
import Solcore.Core.Derived
import Solcore.Core.Eval
import Solcore.Core.ExactFuelProperties
import Solcore.Core.Primitive
import Solcore.Core.Typing

/-!
# Local Core fragment

The local-fragment syntax judgment and its typing, inference, evaluation,
exact-cost insertion, and derived word-less-than properties.
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

/-!
## Exact CEK paths under inserted environments
-/

/-! Paired exact-cost paths for the local Core fragment. A common cost is
chosen before the arbitrary outer continuation. Each side constructs its own
internal frames and saved environments; no equality of states is asserted. -/


namespace Solcore.Core

private theorem lookup_path_environment_insert (leading suffix : Environment) (inserted : Value) (index : Nat) :
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

private theorem pair_path {environment : Environment} {initialStore middleStore finalStore : Store}
    {left right : Expr} {leftValue rightValue : Value}
    {continuation : List Frame} {leftCost rightCost : Nat}
    (leftPath : Steps leftCost
      ⟨.eval left environment, .pairRight right environment :: continuation, initialStore⟩
      ⟨.ret leftValue, .pairRight right environment :: continuation, middleStore⟩)
    (rightPath : Steps rightCost
      ⟨.eval right environment, .pairApply leftValue :: continuation, middleStore⟩
      ⟨.ret rightValue, .pairApply leftValue :: continuation, finalStore⟩) :
    Steps (leftCost + rightCost + 3)
      ⟨.eval (.pair left right) environment, continuation, initialStore⟩
      ⟨.ret (.pair leftValue rightValue), continuation, finalStore⟩ := by
  have path := Steps.cons .enterPair
    (leftPath.trans (.cons .enterPairRight (rightPath.trans (.cons .applyPair .refl))))
  simpa only [Nat.add_assoc] using path

private theorem unary_path {environment : Environment} {initialStore finalStore : Store}
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

private theorem binary_path {environment : Environment} {initialStore middleStore finalStore : Store}
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

private theorem let_path {environment : Environment} {initialStore middleStore finalStore : Store}
    {value body : Expr} {boundValue result : Value} {continuation : List Frame}
    {valueCost bodyCost : Nat}
    (valuePath : Steps valueCost
      ⟨.eval value environment, .letBody body environment :: continuation, initialStore⟩
      ⟨.ret boundValue, .letBody body environment :: continuation, middleStore⟩)
    (bodyPath : Steps bodyCost
      ⟨.eval body (boundValue :: environment), continuation, middleStore⟩
      ⟨.ret result, continuation, finalStore⟩) :
    Steps (valueCost + bodyCost + 2)
      ⟨.eval (.letE value body) environment, continuation, initialStore⟩
      ⟨.ret result, continuation, finalStore⟩ := by
  have path := Steps.cons .enterLet (valuePath.trans (.cons .bindLet bodyPath))
  simpa only [Nat.add_assoc] using path

private theorem if_true_path {environment : Environment} {initialStore middleStore finalStore : Store}
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

private theorem if_false_path {environment : Environment} {initialStore middleStore finalStore : Store}
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

/-- Successful local evaluation gives original and inserted paths with one
shared cost, independent of the untouched outer continuation. Values and both
stores are exact; typing, scope, freshness and runtime-world premises are absent. -/
theorem Expr.LocalFragment.insertion_paths
    {expr : Expr} (fragment : expr.LocalFragment)
    (leading suffix : Environment) (inserted : Value)
    {initialStore finalStore : Store} {value : Value}
    (evaluation : Evaluates (leading ++ suffix) initialStore expr value finalStore) :
    ∃ cost, ∀ continuation,
      Steps cost
        ⟨.eval expr (leading ++ suffix), continuation, initialStore⟩
        ⟨.ret value, continuation, finalStore⟩ ∧
      Steps cost
        ⟨.eval (expr.weakenAt leading.length) (leading ++ inserted :: suffix),
          continuation, initialStore⟩
        ⟨.ret value, continuation, finalStore⟩ := by
  induction fragment generalizing leading initialStore finalStore value with
  | unit =>
      cases evaluation
      simp only [Expr.weakenAt]
      exact ⟨1, fun _ => ⟨.cons .unit .refl, .cons .unit .refl⟩⟩
  | bool =>
      cases evaluation
      simp only [Expr.weakenAt]
      exact ⟨1, fun _ => ⟨.cons .bool .refl, .cons .bool .refl⟩⟩
  | word =>
      cases evaluation
      simp only [Expr.weakenAt]
      exact ⟨1, fun _ => ⟨.cons .word .refl, .cons .word .refl⟩⟩
  | @var index =>
      cases evaluation with
      | var found =>
          refine ⟨1, fun continuation => ⟨.cons (.var found) .refl, ?_⟩⟩
          simp only [Expr.weakenAt]
          have positions := lookup_path_environment_insert leading suffix inserted index
          by_cases shifted : leading.length ≤ index <;>
            simp only [shifted, ↓reduceIte] at positions ⊢
          all_goals exact .cons (.var (positions.trans found)) .refl
  | pair _ _ leftIH rightIH =>
      cases evaluation with
      | pair left right =>
          obtain ⟨leftCost, leftPaths⟩ := leftIH leading left
          obtain ⟨rightCost, rightPaths⟩ := rightIH leading right
          refine ⟨leftCost + rightCost + 3, fun continuation => ?_⟩
          constructor
          · exact pair_path (leftPaths _).1 (rightPaths _).1
          · simp only [Expr.weakenAt]
            exact pair_path (leftPaths _).2 (rightPaths _).2
  | unary _ ih =>
      cases evaluation with
      | unary child applied =>
          obtain ⟨childCost, childPaths⟩ := ih leading child
          refine ⟨childCost + 2, fun continuation => ?_⟩
          constructor
          · exact unary_path (childPaths _).1 applied
          · simp only [Expr.weakenAt]
            exact unary_path (childPaths _).2 applied
  | binary _ _ leftIH rightIH =>
      cases evaluation with
      | binary left right applied =>
          obtain ⟨leftCost, leftPaths⟩ := leftIH leading left
          obtain ⟨rightCost, rightPaths⟩ := rightIH leading right
          refine ⟨leftCost + rightCost + 3, fun continuation => ?_⟩
          constructor
          · exact binary_path (leftPaths _).1 (rightPaths _).1 applied
          · simp only [Expr.weakenAt]
            exact binary_path (leftPaths _).2 (rightPaths _).2 applied
  | letE _ _ valueIH bodyIH =>
      cases evaluation with
      | @letE _ _ _ _ _ _ boundValue _ valueEvaluation bodyEvaluation =>
          obtain ⟨valueCost, valuePaths⟩ := valueIH leading valueEvaluation
          obtain ⟨bodyCost, bodyPaths⟩ := bodyIH (boundValue :: leading) bodyEvaluation
          refine ⟨valueCost + bodyCost + 2, fun continuation => ?_⟩
          constructor
          · exact let_path (valuePaths _).1 (bodyPaths _).1
          · simp only [Expr.weakenAt]
            exact let_path (valuePaths _).2 (bodyPaths _).2
  | ifE _ _ _ conditionIH thenIH elseIH =>
      cases evaluation with
      | ifTrue condition branch =>
          obtain ⟨conditionCost, conditionPaths⟩ := conditionIH leading condition
          obtain ⟨branchCost, branchPaths⟩ := thenIH leading branch
          refine ⟨conditionCost + branchCost + 2, fun continuation => ?_⟩
          constructor
          · exact if_true_path (conditionPaths _).1 (branchPaths _).1
          · simp only [Expr.weakenAt]
            exact if_true_path (conditionPaths _).2 (branchPaths _).2
      | ifFalse condition branch =>
          obtain ⟨conditionCost, conditionPaths⟩ := conditionIH leading condition
          obtain ⟨branchCost, branchPaths⟩ := elseIH leading branch
          refine ⟨conditionCost + branchCost + 2, fun continuation => ?_⟩
          constructor
          · exact if_false_path (conditionPaths _).1 (branchPaths _).1
          · simp only [Expr.weakenAt]
            exact if_false_path (conditionPaths _).2 (branchPaths _).2

end Solcore.Core

/-!
## Exact-cost insertion and reflection
-/

/-! Exact-cost insertion transports a closed final path into any outer
continuation. Only closed final paths are used to identify their lengths;
the continuation is retained, not run, and suspended states may differ. -/


namespace Solcore.Core

theorem Expr.LocalFragment.steps_insert
    {expr : Expr} (fragment : expr.LocalFragment)
    (leading suffix : Environment) (inserted : Value)
    {cost : Nat} {initialStore finalStore : Store} {value : Value}
    (path : Steps cost (State.initial expr (leading ++ suffix) initialStore)
      (State.final value finalStore)) (continuation : List Frame) :
    Steps cost
      ⟨.eval (expr.weakenAt leading.length) (leading ++ inserted :: suffix),
        continuation, initialStore⟩
      ⟨.ret value, continuation, finalStore⟩ := by
  obtain ⟨commonCost, paths⟩ :=
    fragment.insertion_paths leading suffix inserted (steps_from_initial_sound path)
  have sameCost : cost = commonCost := (path.final_unique (paths []).1).1
  exact sameCost.symm ▸ (paths continuation).2

theorem Expr.LocalFragment.steps_reflect_insert
    {expr : Expr} (fragment : expr.LocalFragment)
    (leading suffix : Environment) (inserted : Value)
    {cost : Nat} {initialStore finalStore : Store} {value : Value}
    (path : Steps cost
      (State.initial (expr.weakenAt leading.length) (leading ++ inserted :: suffix) initialStore)
      (State.final value finalStore)) (continuation : List Frame) :
    Steps cost
      ⟨.eval expr (leading ++ suffix), continuation, initialStore⟩
      ⟨.ret value, continuation, finalStore⟩ := by
  have evaluation :=
    (fragment.evaluates_insert_iff leading suffix inserted).mp (steps_from_initial_sound path)
  obtain ⟨commonCost, paths⟩ := fragment.insertion_paths leading suffix inserted evaluation
  have sameCost : cost = commonCost := (path.final_unique (paths []).2).1
  exact sameCost.symm ▸ (paths continuation).1

theorem Expr.LocalFragment.steps_insert_iff
    {expr : Expr} (fragment : expr.LocalFragment)
    (leading suffix : Environment) (inserted : Value)
    {cost : Nat} {initialStore finalStore : Store} {value : Value} :
    Steps cost
      (State.initial (expr.weakenAt leading.length) (leading ++ inserted :: suffix) initialStore)
      (State.final value finalStore) ↔
    Steps cost (State.initial expr (leading ++ suffix) initialStore)
      (State.final value finalStore) :=
  ⟨fun path => fragment.steps_reflect_insert leading suffix inserted path [],
    fun path => fragment.steps_insert leading suffix inserted path []⟩

theorem Steps.weakenAt_zero_localFragment
    {expr : Expr} {environment : Environment} {cost : Nat}
    {initialStore finalStore : Store} {value : Value}
    (path : Steps cost (State.initial expr environment initialStore) (State.final value finalStore))
    (fragment : expr.LocalFragment) (inserted : Value) (continuation : List Frame) :
    Steps cost
      ⟨.eval (expr.weakenAt 0) (inserted :: environment), continuation, initialStore⟩
      ⟨.ret value, continuation, finalStore⟩ :=
  fragment.steps_insert [] environment inserted path continuation

theorem Steps.reflect_weakenAt_zero_localFragment
    {expr : Expr} {environment : Environment} {inserted : Value} {cost : Nat}
    {initialStore finalStore : Store} {value : Value}
    (path : Steps cost (State.initial (expr.weakenAt 0) (inserted :: environment) initialStore)
      (State.final value finalStore))
    (fragment : expr.LocalFragment) (continuation : List Frame) :
    Steps cost
      ⟨.eval expr environment, continuation, initialStore⟩
      ⟨.ret value, continuation, finalStore⟩ :=
  fragment.steps_reflect_insert [] environment inserted path continuation

end Solcore.Core

/-!
## Ordered comparison typing
-/

/-! Static local-fragment facts for the existing ordered Word less-than
expansion. Only the right operand needs the fragment restriction for typing
reflection; the left operand may use arbitrary Core syntax. -/


namespace Solcore.Core

theorem Expr.LocalFragment.wordLt {left right : Expr}
    (leftFragment : left.LocalFragment) (rightFragment : right.LocalFragment) :
    (left.wordLt right).LocalFragment := by
  rw [Expr.wordLt_expansion]
  exact .letE leftFragment (.letE (rightFragment.weakenAt 0) (.binary .var .var))

/-- Invert the retained Word bindings, then recover typing of the original
right operand. Data definitions and the original context are arbitrary. -/
theorem HasType.wordLt_inv_local_right
    {context : Context} {left right : Expr} {type : Ty} {definitions : DataEnvironment}
    (typing : HasType context (left.wordLt right) type definitions)
    (rightFragment : right.LocalFragment) :
    type = .bool ∧ HasType context left .word definitions ∧
      HasType context right .word definitions := by
  rw [Expr.wordLt_expansion] at typing
  cases typing with
  | @letE _ _ _ _ leftType _ leftTyping innerTyping =>
      cases innerTyping with
      | @letE _ _ _ _ rightType _ rightTyping comparison =>
          cases comparison with
          | binary rightReference leftReference =>
              cases rightReference with
              | var foundRight =>
                  cases leftReference with
                  | var foundLeft =>
                      have rightTypeEq : rightType = .word := by
                        simpa [BinaryOp.leftType] using foundRight
                      have leftTypeEq : leftType = .word := by
                        simpa [BinaryOp.rightType] using foundLeft
                      cases rightTypeEq
                      cases leftTypeEq
                      exact ⟨rfl, leftTyping,
                        rightTyping.reflect_weakenAt_zero_localFragment rightFragment⟩

end Solcore.Core

/-!
## Ordered comparison evaluation
-/

/-! Untyped ordered evaluation of the existing Word less-than expansion.
Only the right operand is restricted; left effects and all three actual stores
are retained. These results do not assume typed runtime values or stores. -/


namespace Solcore.Core

theorem Evaluates.wordLt_local_right
    {environment : Environment} {initialStore middleStore finalStore : Store}
    {left right : Expr} {leftWord rightWord : Word}
    (leftEvaluation : Evaluates environment initialStore left (.word leftWord) middleStore)
    (rightEvaluation : Evaluates environment middleStore right (.word rightWord) finalStore)
    (rightFragment : right.LocalFragment) :
    Evaluates environment initialStore (left.wordLt right)
      (.bool (decide (leftWord < rightWord))) finalStore := by
  rw [Expr.wordLt_expansion]
  exact .letE leftEvaluation
    (.letE (rightEvaluation.weakenAt_zero_localFragment rightFragment (.word leftWord))
      (.binary (.var rfl) (.var rfl) rfl))

/-- Recover the original operand evaluations and the actual intermediate store,
not merely the evaluation of the shifted right operand beneath its new binding. -/
theorem Evaluates.wordLt_inv_local_right
    {environment : Environment} {initialStore finalStore : Store}
    {left right : Expr} {value : Value}
    (evaluation : Evaluates environment initialStore (left.wordLt right) value finalStore)
    (rightFragment : right.LocalFragment) :
    ∃ leftWord rightWord middleStore,
      Evaluates environment initialStore left (.word leftWord) middleStore ∧
      Evaluates environment middleStore right (.word rightWord) finalStore ∧
      value = .bool (decide (leftWord < rightWord)) := by
  rw [Expr.wordLt_expansion] at evaluation
  cases evaluation with
  | @letE _ _ _ _ _ _ boundLeft _ leftEvaluation bodyEvaluation =>
      cases bodyEvaluation with
      | @letE _ _ _ _ _ _ boundRight _ rightEvaluation comparison =>
          cases comparison with
          | @binary _ _ _ _ _ _ _ rightValue leftValue _ rightReference leftReference applied =>
              cases rightReference with
              | var foundRight =>
                  have rightEq : boundRight = rightValue := by simpa using foundRight
                  subst rightValue
                  cases leftReference with
                  | var foundLeft =>
                      have leftEq : boundLeft = leftValue := by simpa using foundLeft
                      subst leftValue
                      cases boundRight <;> cases boundLeft <;>
                        simp only [BinaryOp.apply, reduceCtorEq] at applied
                      case word.word rightWord leftWord =>
                        cases applied
                        exact ⟨leftWord, rightWord, _, leftEvaluation,
                          rightEvaluation.reflect_weakenAt_zero_localFragment rightFragment, rfl⟩

theorem wordLt_evaluates_iff_local_right
    {environment : Environment} {initialStore finalStore : Store}
    {left right : Expr} {value : Value} (rightFragment : right.LocalFragment) :
    Evaluates environment initialStore (left.wordLt right) value finalStore ↔
      ∃ leftWord rightWord middleStore,
        Evaluates environment initialStore left (.word leftWord) middleStore ∧
        Evaluates environment middleStore right (.word rightWord) finalStore ∧
        value = .bool (decide (leftWord < rightWord)) := by
  constructor
  · intro evaluation
    exact evaluation.wordLt_inv_local_right rightFragment
  · rintro ⟨leftWord, rightWord, middleStore, leftEvaluation, rightEvaluation, rfl⟩
    exact leftEvaluation.wordLt_local_right rightEvaluation rightFragment

end Solcore.Core
