import Solcore.Frontend.RecursiveLocalComputationCostExecutionProperties
import Solcore.Frontend.RecursiveLocalComputationEvaluationProperties
import Solcore.Frontend.LocalExpressionEvaluationProperties
import Solcore.Frontend.RecursiveLocalComputationFragmentInsertionProperties

/-! Existing execution contracts retain original-source evidence.
Forward success uses the exact cost path; reverse success is independent induction. -/

set_option autoImplicit false

namespace Solcore.Frontend

private theorem ordered_inv {environment : Core.Environment}
    {initialStore finalStore : Core.Store} {left right : Core.Expr} {value : Core.Value}
    (evaluation : Core.Evaluates environment initialStore (left.wordLt right) value finalStore)
    (rightFragment : RecursiveLocalComputationFragment right) :
    ∃ leftWord rightWord middleStore,
      Core.Evaluates environment initialStore left (.word leftWord) middleStore ∧
      Core.Evaluates environment middleStore right (.word rightWord) finalStore ∧
      value = .bool (decide (leftWord < rightWord)) := by
  rw [Core.Expr.wordLt_expansion] at evaluation
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
                        simp only [Core.BinaryOp.apply, reduceCtorEq] at applied
                      case word.word rightWord leftWord =>
                        cases applied
                        exact ⟨leftWord, rightWord, _, leftEvaluation,
                          (rightFragment.evaluates_insert_iff [] environment (.word leftWord)).mp rightEvaluation, rfl⟩

theorem RecursiveLocalComputationElaborates.evaluates_iff
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (elaboration : RecursiveLocalComputationElaborates table context source core type)
    (sameIds : environment.ids = context.ids)
    {initialStore finalStore : Core.Store} {value : Core.Value} :
    RecursiveLocalComputationEvaluates table environment initialStore source value finalStore ↔
      Core.Evaluates environment.values initialStore core value finalStore := by
  constructor
  · intro evaluation
    obtain ⟨_, costed⟩ := recursiveLocalComputationEvaluates_iff_exists_cost.mp evaluation
    exact Core.steps_from_initial_sound (costed.toStepsWithContinuation elaboration sameIds [])
  · intro evaluation
    induction elaboration generalizing initialStore finalStore value with
    | pure resolution lowered _ =>
        rw [← sameIds] at lowered
        exact .pure ((resolution.core_evaluates_iff lowered).mpr evaluation)
    | group _ ih => exact .group (ih evaluation)
    | application _ _ functionIH argumentIH =>
        cases evaluation with
        | apply functionEvaluation argumentEvaluation bodyEvaluation =>
            exact .application (functionIH functionEvaluation) (argumentIH argumentEvaluation) bodyEvaluation
    | binary operator _ _ leftIH rightIH =>
        cases evaluation with
        | binary leftChild rightChild applied => exact .binary operator (leftIH leftChild) (rightIH rightChild) applied
    | conditional _ _ _ conditionIH thenIH elseIH =>
        cases evaluation with
        | ifTrue guard branch => exact .ifTrue (conditionIH guard) (thenIH branch)
        | ifFalse guard branch => exact .ifFalse (conditionIH guard) (elseIH branch)
    | logicalNot _ ih =>
        cases evaluation with
        | @unary _ _ _ _ _ childValue _ child applied =>
            cases childValue <;> cases applied
            exact .logicalNot (ih child)
    | bitNot _ ih =>
        cases evaluation with
        | @unary _ _ _ _ _ childValue _ child applied =>
            cases childValue <;> cases applied
            exact .bitNot (ih child)
    | logicalAnd _ _ leftIH rightIH =>
        cases evaluation with
        | ifTrue left right => exact .andTrue (leftIH left) (rightIH right)
        | ifFalse left constant =>
            cases constant
            exact .andFalse (leftIH left)
    | logicalOr _ _ leftIH rightIH =>
        cases evaluation with
        | ifTrue left constant =>
            cases constant
            exact .orTrue (leftIH left)
        | ifFalse left right => exact .orFalse (leftIH left) (rightIH right)
    | notEqual _ _ leftIH rightIH =>
        cases evaluation with
        | unary comparison negated =>
            cases comparison with
            | @binary _ _ _ _ _ _ _ leftValue rightValue _ left right compared =>
                cases leftValue <;> cases rightValue <;> cases compared <;> cases negated
                exact .notEqual (leftIH left) (rightIH right)
    | lessEqual _ _ leftIH rightIH =>
        cases evaluation with
        | unary comparison negated =>
            cases comparison with
            | @binary _ _ _ _ _ _ _ leftValue rightValue _ left right compared =>
                cases leftValue <;> cases rightValue <;> cases compared <;> cases negated
                exact .lessEqual (leftIH left) (rightIH right)

    | less _ rightElab leftIH rightIH =>
        obtain ⟨_, _, _, left, right, rfl⟩ := ordered_inv evaluation rightElab.core_fragment
        exact .less (leftIH left) (rightIH right)
    | greaterEqual _ rightElab leftIH rightIH =>
        cases evaluation with
        | unary comparison negated =>
            obtain ⟨_, _, _, left, right, rfl⟩ := ordered_inv comparison rightElab.core_fragment
            cases negated
            exact .greaterEqual (leftIH left) (rightIH right)

theorem RecursiveLocalComputationElaborates.evaluatesWithCost_iff_steps
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (elaboration : RecursiveLocalComputationElaborates table context source core type)
    (sameIds : environment.ids = context.ids)
    {initialStore finalStore : Core.Store} {value : Core.Value} {cost : Nat} :
    RecursiveLocalComputationEvaluatesWithCost table environment initialStore source value finalStore cost ↔
      Core.Steps cost (.initial core environment.values initialStore) (.final value finalStore) := by
  constructor
  · intro evaluation
    exact evaluation.toStepsWithContinuation elaboration sameIds []
  · intro path
    have evaluation := (elaboration.evaluates_iff sameIds).mpr (Core.steps_from_initial_sound path)
    obtain ⟨actualCost, actual⟩ := recursiveLocalComputationEvaluates_iff_exists_cost.mp evaluation
    have sameCost := (path.final_unique (actual.toStepsWithContinuation elaboration sameIds [])).1
    exact sameCost.symm ▸ actual

end Solcore.Frontend
