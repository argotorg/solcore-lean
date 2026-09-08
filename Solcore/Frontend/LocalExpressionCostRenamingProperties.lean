import Solcore.Frontend.LocalExpressionCostProperties
import Solcore.Frontend.LocalExpressionRenamingSemantics

/-! Injective identity relabeling preserves independent source costs. Only
identifier leaves use erased evaluation to recover the existing lookup laws. -/

set_option autoImplicit false

namespace Solcore.Frontend

/-- Simultaneous injective ID relabeling preserves raw value, both stores, and
cost. Whole resolution and typing are not required, even for skipped syntax. -/
theorem localExpressionEvaluatesWithCost_mapIds_iff
    (mapping : Resolved.LocalId → Resolved.LocalId) (injective : Function.Injective mapping)
    {table : LocalNameTable} {environment : Resolved.Environment} {source : Syntax.Expr}
    {initialStore finalStore : Core.Store} {value : Core.Value} {cost : Nat} :
    LocalExpressionEvaluatesWithCost (LocalNameTable.mapIds mapping table)
        (Resolved.LocalScope.mapIds mapping environment) initialStore source value finalStore cost ↔
      LocalExpressionEvaluatesWithCost table environment initialStore source value finalStore cost := by
  constructor
  · intro evaluation
    induction evaluation with
    | @identifier store span name id value named found =>
        have ordinary := (localExpressionEvaluates_mapIds_iff mapping injective).mp
          (LocalExpressionEvaluatesWithCost.identifier (store := store) (span := span) named found).erase
        cases ordinary with
        | identifier oldNamed oldFound => exact .identifier oldNamed oldFound
    | wordLiteral meaning => exact .wordLiteral meaning
    | unit => exact .unit
    | group _ ih => exact .group ih
    | pair _ _ leftIH rightIH => exact .pair leftIH rightIH
    | logicalNot _ ih => exact .logicalNot ih
    | bitNot _ ih => exact .bitNot ih
    | add _ _ leftIH rightIH => exact .add leftIH rightIH
    | subtract _ _ leftIH rightIH => exact .subtract leftIH rightIH
    | multiply _ _ leftIH rightIH => exact .multiply leftIH rightIH
    | divide _ _ leftIH rightIH => exact .divide leftIH rightIH
    | modulo _ _ leftIH rightIH => exact .modulo leftIH rightIH
    | greater _ _ leftIH rightIH => exact .greater leftIH rightIH
    | less _ _ leftIH rightIH => exact .less leftIH rightIH
    | equal _ _ leftIH rightIH => exact .equal leftIH rightIH
    | notEqual _ _ leftIH rightIH => exact .notEqual leftIH rightIH
    | lessEqual _ _ leftIH rightIH => exact .lessEqual leftIH rightIH
    | greaterEqual _ _ leftIH rightIH => exact .greaterEqual leftIH rightIH
    | bitAnd _ _ leftIH rightIH => exact .bitAnd leftIH rightIH
    | bitOr _ _ leftIH rightIH => exact .bitOr leftIH rightIH
    | bitXor _ _ leftIH rightIH => exact .bitXor leftIH rightIH
    | andTrue _ _ leftIH rightIH => exact .andTrue leftIH rightIH
    | andFalse _ ih => exact .andFalse ih
    | orTrue _ ih => exact .orTrue ih
    | orFalse _ _ leftIH rightIH => exact .orFalse leftIH rightIH
    | ifTrue _ _ conditionIH branchIH => exact .ifTrue conditionIH branchIH
    | ifFalse _ _ conditionIH branchIH => exact .ifFalse conditionIH branchIH
  · intro evaluation
    induction evaluation with
    | @identifier store span name id value named found =>
        have ordinary := (localExpressionEvaluates_mapIds_iff mapping injective).mpr
          (LocalExpressionEvaluatesWithCost.identifier (store := store) (span := span) named found).erase
        cases ordinary with
        | identifier newNamed newFound => exact .identifier newNamed newFound
    | wordLiteral meaning => exact .wordLiteral meaning
    | unit => exact .unit
    | group _ ih => exact .group ih
    | pair _ _ leftIH rightIH => exact .pair leftIH rightIH
    | logicalNot _ ih => exact .logicalNot ih
    | bitNot _ ih => exact .bitNot ih
    | add _ _ leftIH rightIH => exact .add leftIH rightIH
    | subtract _ _ leftIH rightIH => exact .subtract leftIH rightIH
    | multiply _ _ leftIH rightIH => exact .multiply leftIH rightIH
    | divide _ _ leftIH rightIH => exact .divide leftIH rightIH
    | modulo _ _ leftIH rightIH => exact .modulo leftIH rightIH
    | greater _ _ leftIH rightIH => exact .greater leftIH rightIH
    | less _ _ leftIH rightIH => exact .less leftIH rightIH
    | equal _ _ leftIH rightIH => exact .equal leftIH rightIH
    | notEqual _ _ leftIH rightIH => exact .notEqual leftIH rightIH
    | lessEqual _ _ leftIH rightIH => exact .lessEqual leftIH rightIH
    | greaterEqual _ _ leftIH rightIH => exact .greaterEqual leftIH rightIH
    | bitAnd _ _ leftIH rightIH => exact .bitAnd leftIH rightIH
    | bitOr _ _ leftIH rightIH => exact .bitOr leftIH rightIH
    | bitXor _ _ leftIH rightIH => exact .bitXor leftIH rightIH
    | andTrue _ _ leftIH rightIH => exact .andTrue leftIH rightIH
    | andFalse _ ih => exact .andFalse ih
    | orTrue _ ih => exact .orTrue ih
    | orFalse _ _ leftIH rightIH => exact .orFalse leftIH rightIH
    | ifTrue _ _ conditionIH branchIH => exact .ifTrue conditionIH branchIH
    | ifFalse _ _ conditionIH branchIH => exact .ifFalse conditionIH branchIH

end Solcore.Frontend
