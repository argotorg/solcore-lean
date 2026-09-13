import Solcore.Frontend.ClosedSourceEvaluationCompatibility

/- Original closed source rules neither inspect nor mutate stores. Replaying a
value keeps source, lexical rows and opaque captured values literal; replacing
the store does not establish validity of any cell reference inside those values. -/
set_option autoImplicit false
namespace Solcore.Frontend

/-- Every successful original expression returns its actual initial store unchanged. -/
theorem ClosedSourceExpressionEvaluates.store_eq
    {owner names captured initialStore source value finalStore}
    (original : ClosedSourceExpressionEvaluates owner names captured initialStore source value finalStore) :
    finalStore = initialStore := by
  induction original using ClosedSourceExpressionEvaluates.rec
    (motive_2 := fun _ _ _ store _ _ final _ => final = store) <;> simp_all

/-- Every successful original body returns its actual initial store unchanged. -/
theorem ClosedSourceBodyEvaluates.store_eq
    {owner names captured initialStore source value finalStore}
    (original : ClosedSourceBodyEvaluates owner names captured initialStore source value finalStore) :
    finalStore = initialStore := by
  induction original using ClosedSourceBodyEvaluates.rec
    (motive_1 := fun _ _ _ store _ _ final _ => final = store) <;> simp_all

/-- Original expression success replays the same complete value from any store.
No lexical, typing, scope or runtime-world premise is added. -/
theorem ClosedSourceExpressionEvaluates.replay_store
    {owner names captured initialStore source value finalStore}
    (original : ClosedSourceExpressionEvaluates owner names captured initialStore source value finalStore)
    (replacement : List RuntimeValue) :
    ClosedSourceExpressionEvaluates owner names captured replacement source value replacement := by
  induction original using ClosedSourceExpressionEvaluates.rec
    (motive_2 := fun owner names captured _ source value _ _ =>
      ∀ replacement, ClosedSourceBodyEvaluates owner names captured replacement source value replacement) generalizing replacement with
  | reference named found => exact .reference named found
  | unit => exact .unit
  | wordLiteral meaning => exact .wordLiteral meaning
  | group _ ih => exact .group (ih replacement)
  | pair _ _ leftIH rightIH => exact .pair (leftIH replacement) (rightIH replacement)
  | many _ _ headIH tailIH => exact .many (headIH replacement) (tailIH replacement)
  | creation shape => exact .creation shape
  | call shape _ _ _ calleeIH argumentIH bodyIH =>
    exact .call shape (calleeIH replacement) (argumentIH replacement) (bodyIH replacement)
  | conditionalTrue _ _ conditionIH branchIH => exact .conditionalTrue (conditionIH replacement) (branchIH replacement)
  | conditionalFalse _ _ conditionIH branchIH => exact .conditionalFalse (conditionIH replacement) (branchIH replacement)
  | logicalNot _ ih => exact .logicalNot (ih replacement)
  | bitNot _ ih => exact .bitNot (ih replacement)
  | andTrue _ _ leftIH rightIH => exact .andTrue (leftIH replacement) (rightIH replacement)
  | andFalse _ ih => exact .andFalse (ih replacement)
  | orTrue _ ih => exact .orTrue (ih replacement)
  | orFalse _ _ leftIH rightIH => exact .orFalse (leftIH replacement) (rightIH replacement)
  | strictWordBinary _ _ meaning leftIH rightIH => exact .strictWordBinary (leftIH replacement) (rightIH replacement) meaning
  | bare => exact .bare
  | expression _ ih => rename_i replacement; exact .expression (ih replacement)
  | block _ ih => rename_i replacement; exact .block (ih replacement)
  | binding _ _ initializerIH tailIH => rename_i replacement; exact .binding (initializerIH replacement) (tailIH replacement)
  | inferred _ _ initializerIH tailIH => rename_i replacement; exact .inferred (initializerIH replacement) (tailIH replacement)
  | discard _ _ expressionIH tailIH => rename_i replacement; exact .discard (expressionIH replacement) (tailIH replacement)
  | ifTrue _ _ conditionIH branchIH => rename_i replacement; exact .ifTrue (conditionIH replacement) (branchIH replacement)
  | ifFalse _ _ conditionIH branchIH => rename_i replacement; exact .ifFalse (conditionIH replacement) (branchIH replacement)
  | wordMatch _ choice _ scrutineeIH branchIH =>
    rename_i replacement; exact .wordMatch (scrutineeIH replacement) choice (branchIH replacement)

/-- Original body replay preserves all actual values and fresh saved lexical inputs. -/
theorem ClosedSourceBodyEvaluates.replay_store
    {owner names captured initialStore source value finalStore}
    (original : ClosedSourceBodyEvaluates owner names captured initialStore source value finalStore)
    (replacement : List RuntimeValue) :
    ClosedSourceBodyEvaluates owner names captured replacement source value replacement := by
  have compatible := closedSourceBodyEvaluates_iff.mp original
  clear original
  apply closedSourceBodyEvaluates_iff.mpr
  induction compatible with
  | bare => exact .bare
  | expression child => exact .expression (child.replay_store replacement)
  | block _ ih => exact .block ih
  | binding initializer _ ih => exact .binding (initializer.replay_store replacement) ih
  | inferred initializer _ ih => exact .inferred (initializer.replay_store replacement) ih
  | discard expression _ ih => exact .discard (expression.replay_store replacement) ih
  | ifTrue condition _ ih => exact .ifTrue (condition.replay_store replacement) ih
  | ifFalse condition _ ih => exact .ifFalse (condition.replay_store replacement) ih
  | wordMatch scrutinee choice _ ih => exact .wordMatch (scrutinee.replay_store replacement) choice ih

end Solcore.Frontend
