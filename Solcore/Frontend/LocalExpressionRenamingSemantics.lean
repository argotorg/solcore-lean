import Solcore.Frontend.LocalExpressionRenamingProperties
import Solcore.Frontend.LocalExpressionTypingProperties
import Solcore.Frontend.LocalExpressionEvaluation
import Solcore.Resolved.RenamingProperties

/-! Simultaneous injective relabeling preserves checking and raw evaluation
of the same source AST. Names, values, types, and both stores are unchanged;
no whole-resolution or typing premise is added to evaluation invariance. -/

set_option autoImplicit false

namespace Solcore.Frontend

/-- Positional Core and its type are exactly unchanged, including failures. -/
theorem elaborateLocalExpression?_mapIds (mapping : Resolved.LocalId → Resolved.LocalId)
    (injective : Function.Injective mapping) (table : LocalNameTable)
    (context : Resolved.Context) (source : Syntax.Expr) :
    elaborateLocalExpression? (LocalNameTable.mapIds mapping table)
        (Resolved.LocalScope.mapIds mapping context) source =
      elaborateLocalExpression? table context source := by
  cases resolved : resolveLocalExpression? table source with
  | none =>
      simp [elaborateLocalExpression?, resolveLocalExpression?_mapIds, resolved]
  | some expr =>
      simp [elaborateLocalExpression?, resolveLocalExpression?_mapIds, resolved,
        Resolved.Expr.lower?_renameIds mapping injective]

theorem localExpressionHasType_mapIds_iff (mapping : Resolved.LocalId → Resolved.LocalId)
    (injective : Function.Injective mapping) {table : LocalNameTable}
    {context : Resolved.Context} {source : Syntax.Expr} {type : Core.Ty} :
    LocalExpressionHasType (LocalNameTable.mapIds mapping table)
        (Resolved.LocalScope.mapIds mapping context) source type ↔
      LocalExpressionHasType table context source type := by
  rw [localExpressionHasType_iff_elaborates, localExpressionHasType_iff_elaborates]
  simp only [elaborateLocalExpression?_mapIds mapping injective]

/-- Raw evaluation preserves arbitrary selected right values and can skip
unresolved or unsupported syntax. No typing or whole-resolution assumption
is needed, even when the original tables repeat names or alias identities. -/
theorem localExpressionEvaluates_mapIds_iff (mapping : Resolved.LocalId → Resolved.LocalId)
    (injective : Function.Injective mapping) {table : LocalNameTable}
    {environment : Resolved.Environment} {source : Syntax.Expr}
    {initialStore finalStore : Core.Store} {value : Core.Value} :
    LocalExpressionEvaluates (LocalNameTable.mapIds mapping table)
        (Resolved.LocalScope.mapIds mapping environment) initialStore source value finalStore ↔
      LocalExpressionEvaluates table environment initialStore source value finalStore := by
  constructor
  · intro evaluation
    induction evaluation with
    | identifier named found =>
        obtain ⟨id, oldNamed, same⟩ := (LocalNameTable.lookup_mapIds_iff_exists mapping).mp named
        rw [← same] at found
        exact .identifier oldNamed ((Resolved.LocalScope.lookup_mapIds_iff mapping injective).mp found)
    | wordLiteral meaning => exact .wordLiteral meaning
    | group _ ih => exact .group ih
    | logicalNot _ ih => exact .logicalNot ih
    | bitNot _ ih => exact .bitNot ih
    | add _ _ leftIH rightIH => exact .add leftIH rightIH
    | subtract _ _ leftIH rightIH => exact .subtract leftIH rightIH
    | multiply _ _ leftIH rightIH => exact .multiply leftIH rightIH
    | greater _ _ leftIH rightIH => exact .greater leftIH rightIH
    | equal _ _ leftIH rightIH => exact .equal leftIH rightIH
    | notEqual _ _ leftIH rightIH => exact .notEqual leftIH rightIH
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
    | identifier named found =>
        exact .identifier ((LocalNameTable.lookup_mapIds_iff mapping injective).mpr named)
          ((Resolved.LocalScope.lookup_mapIds_iff mapping injective).mpr found)
    | wordLiteral meaning => exact .wordLiteral meaning
    | group _ ih => exact .group ih
    | logicalNot _ ih => exact .logicalNot ih
    | bitNot _ ih => exact .bitNot ih
    | add _ _ leftIH rightIH => exact .add leftIH rightIH
    | subtract _ _ leftIH rightIH => exact .subtract leftIH rightIH
    | multiply _ _ leftIH rightIH => exact .multiply leftIH rightIH
    | greater _ _ leftIH rightIH => exact .greater leftIH rightIH
    | equal _ _ leftIH rightIH => exact .equal leftIH rightIH
    | notEqual _ _ leftIH rightIH => exact .notEqual leftIH rightIH
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
