import Solcore.Core.Correspondence
import Solcore.Core.Derived
import Solcore.Core.ExactFuelProperties
import Solcore.Core.LocalFragment.Basic
import Solcore.Core.LocalFragment.RuntimeSafety

/-!
# Local Core fragment

The local-fragment syntax judgment and its typing, inference, evaluation,
exact-cost insertion, and derived word-less-than properties.
-/

set_option autoImplicit false

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
