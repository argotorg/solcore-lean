import Solcore.Frontend.RecursiveLocalComputationEvaluationProperties
import Solcore.Frontend.LocalExpressionCostRenamingProperties

/-! Raw identity relabeling keeps actual values, captured Core paths and all
stores/costs fixed. No checking, typing, scope alignment or runtime world is
required; neither successful evaluation nor its absence classifies faults. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem recursiveLocalComputationEvaluatesWithCost_mapIds_iff
    (mapping : Resolved.LocalId → Resolved.LocalId) (injective : Function.Injective mapping)
    {table : LocalNameTable} {environment : Resolved.Environment} {source : Syntax.Expr}
    {initialStore finalStore : Core.Store} {value : Core.Value} {cost : Nat} :
    RecursiveLocalComputationEvaluatesWithCost (LocalNameTable.mapIds mapping table)
        (Resolved.LocalScope.mapIds mapping environment) initialStore source value finalStore cost ↔
      RecursiveLocalComputationEvaluatesWithCost table environment initialStore source value finalStore cost := by
  constructor
  · intro evaluation
    induction evaluation with
    | pure child => exact .pure ((localExpressionEvaluatesWithCost_mapIds_iff mapping injective).mp child)
    | group _ ih => exact .group ih
    | application _ _ bodyPath functionIH argumentIH => exact .application functionIH argumentIH bodyPath
    | pair _ _ leftIH rightIH => exact .pair leftIH rightIH
    | many _ _ headIH tailIH => exact .many headIH tailIH
    | binary operator _ _ applied leftIH rightIH => exact .binary operator leftIH rightIH applied
    | ifTrue _ _ conditionIH branchIH => exact .ifTrue conditionIH branchIH
    | ifFalse _ _ conditionIH branchIH => exact .ifFalse conditionIH branchIH
    | logicalNot _ ih => exact .logicalNot ih
    | bitNot _ ih => exact .bitNot ih
    | andTrue _ _ leftIH rightIH => exact .andTrue leftIH rightIH
    | andFalse _ ih => exact .andFalse ih
    | orTrue _ ih => exact .orTrue ih
    | orFalse _ _ leftIH rightIH => exact .orFalse leftIH rightIH
    | notEqual _ _ leftIH rightIH => exact .notEqual leftIH rightIH
    | lessEqual _ _ leftIH rightIH => exact .lessEqual leftIH rightIH
    | less _ _ leftIH rightIH => exact .less leftIH rightIH
    | greaterEqual _ _ leftIH rightIH => exact .greaterEqual leftIH rightIH
  · intro evaluation
    induction evaluation with
    | pure child => exact .pure ((localExpressionEvaluatesWithCost_mapIds_iff mapping injective).mpr child)
    | group _ ih => exact .group ih
    | application _ _ bodyPath functionIH argumentIH => exact .application functionIH argumentIH bodyPath
    | pair _ _ leftIH rightIH => exact .pair leftIH rightIH
    | many _ _ headIH tailIH => exact .many headIH tailIH
    | binary operator _ _ applied leftIH rightIH => exact .binary operator leftIH rightIH applied
    | ifTrue _ _ conditionIH branchIH => exact .ifTrue conditionIH branchIH
    | ifFalse _ _ conditionIH branchIH => exact .ifFalse conditionIH branchIH
    | logicalNot _ ih => exact .logicalNot ih
    | bitNot _ ih => exact .bitNot ih
    | andTrue _ _ leftIH rightIH => exact .andTrue leftIH rightIH
    | andFalse _ ih => exact .andFalse ih
    | orTrue _ ih => exact .orTrue ih
    | orFalse _ _ leftIH rightIH => exact .orFalse leftIH rightIH
    | notEqual _ _ leftIH rightIH => exact .notEqual leftIH rightIH
    | lessEqual _ _ leftIH rightIH => exact .lessEqual leftIH rightIH
    | less _ _ leftIH rightIH => exact .less leftIH rightIH
    | greaterEqual _ _ leftIH rightIH => exact .greaterEqual leftIH rightIH

/-- Successful raw evaluation and its absence are both reflected. An actual
selected non-Bool lazy RHS remains allowed by these untyped raw rules. -/
theorem recursiveLocalComputationEvaluates_mapIds_iff
    (mapping : Resolved.LocalId → Resolved.LocalId) (injective : Function.Injective mapping)
    {table : LocalNameTable} {environment : Resolved.Environment} {source : Syntax.Expr}
    {initialStore finalStore : Core.Store} {value : Core.Value} :
    RecursiveLocalComputationEvaluates (LocalNameTable.mapIds mapping table)
        (Resolved.LocalScope.mapIds mapping environment) initialStore source value finalStore ↔
      RecursiveLocalComputationEvaluates table environment initialStore source value finalStore := by
  simp only [recursiveLocalComputationEvaluates_iff_exists_cost,
    recursiveLocalComputationEvaluatesWithCost_mapIds_iff mapping injective]

end Solcore.Frontend
