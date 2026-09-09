import Solcore.Frontend.RecursiveLocalComputationProperties
import Solcore.Frontend.LocalExpressionRenamingProperties
import Solcore.Resolved.RenamingProperties

/-! Simultaneous injective identity relabeling retains original recursive
source evidence and exact positional Core. No source binder is allocated here;
owner and binder-index changes need neither an inverse nor runtime values. -/

set_option autoImplicit false

namespace Solcore.Frontend

/-- Reflect the original resolved child at pure leaves; recursive rules retain
their own evidence even when the source also belongs to the pure fragment. -/
theorem recursiveLocalComputationElaborates_mapIds_iff
    (mapping : Resolved.LocalId → Resolved.LocalId) (injective : Function.Injective mapping)
    {table : LocalNameTable} {context : Resolved.Context} {source : Syntax.Expr}
    {core : Core.Expr} {type : Core.Ty} :
    RecursiveLocalComputationElaborates (LocalNameTable.mapIds mapping table)
        (Resolved.LocalScope.mapIds mapping context) source core type ↔
      RecursiveLocalComputationElaborates table context source core type := by
  constructor
  · intro elaboration
    induction elaboration with
    | pure resolution lowered typing =>
        obtain ⟨original, originalResolution, rfl⟩ :=
          (resolvesLocalExpression_mapIds_iff_exists mapping).mp resolution
        exact .pure originalResolution
          ((Resolved.lowers_renameIds_iff mapping injective).mp
            (by simpa only [Resolved.LocalScope.ids_mapIds] using lowered))
          ((Resolved.typing_renameIds_iff mapping injective).mp typing)
    | group _ ih => exact .group ih
    | application _ _ functionIH argumentIH => exact .application functionIH argumentIH
    | pair _ _ leftIH rightIH => exact .pair leftIH rightIH
    | many _ _ headIH tailIH => exact .many headIH tailIH
    | binary operator _ _ leftIH rightIH => exact .binary operator leftIH rightIH
    | conditional _ _ _ conditionIH thenIH elseIH => exact .conditional conditionIH thenIH elseIH
    | logicalNot _ ih => exact .logicalNot ih
    | bitNot _ ih => exact .bitNot ih
    | logicalAnd _ _ leftIH rightIH => exact .logicalAnd leftIH rightIH
    | logicalOr _ _ leftIH rightIH => exact .logicalOr leftIH rightIH
    | notEqual _ _ leftIH rightIH => exact .notEqual leftIH rightIH
    | lessEqual _ _ leftIH rightIH => exact .lessEqual leftIH rightIH
    | less _ _ leftIH rightIH => exact .less leftIH rightIH
    | greaterEqual _ _ leftIH rightIH => exact .greaterEqual leftIH rightIH
  · intro elaboration
    induction elaboration with
    | pure resolution lowered typing =>
        exact .pure (resolution.mapIds mapping)
          (by simpa only [Resolved.LocalScope.ids_mapIds] using
            (Resolved.lowers_renameIds_iff mapping injective).mpr lowered)
          ((Resolved.typing_renameIds_iff mapping injective).mpr typing)
    | group _ ih => exact .group ih
    | application _ _ functionIH argumentIH => exact .application functionIH argumentIH
    | pair _ _ leftIH rightIH => exact .pair leftIH rightIH
    | many _ _ headIH tailIH => exact .many headIH tailIH
    | binary operator _ _ leftIH rightIH => exact .binary operator leftIH rightIH
    | conditional _ _ _ conditionIH thenIH elseIH => exact .conditional conditionIH thenIH elseIH
    | logicalNot _ ih => exact .logicalNot ih
    | bitNot _ ih => exact .bitNot ih
    | logicalAnd _ _ leftIH rightIH => exact .logicalAnd leftIH rightIH
    | logicalOr _ _ leftIH rightIH => exact .logicalOr leftIH rightIH
    | notEqual _ _ leftIH rightIH => exact .notEqual leftIH rightIH
    | lessEqual _ _ leftIH rightIH => exact .lessEqual leftIH rightIH
    | less _ _ leftIH rightIH => exact .less leftIH rightIH
    | greaterEqual _ _ leftIH rightIH => exact .greaterEqual leftIH rightIH

theorem recursiveLocalComputationHasType_mapIds_iff
    (mapping : Resolved.LocalId → Resolved.LocalId) (injective : Function.Injective mapping)
    {table : LocalNameTable} {context : Resolved.Context} {source : Syntax.Expr} {type : Core.Ty} :
    RecursiveLocalComputationHasType (LocalNameTable.mapIds mapping table)
        (Resolved.LocalScope.mapIds mapping context) source type ↔
      RecursiveLocalComputationHasType table context source type := by
  simp only [recursiveLocalComputationHasType_iff_elaborates,
    recursiveLocalComputationElaborates_mapIds_iff mapping injective]

/-- Complete checking agrees, including rejected original children. Injectivity
does not require surjectivity, unique caller rows or an owner-only map. -/
theorem elaborateRecursiveLocalComputation?_mapIds
    (mapping : Resolved.LocalId → Resolved.LocalId) (injective : Function.Injective mapping)
    (table : LocalNameTable) (context : Resolved.Context) (source : Syntax.Expr) :
    elaborateRecursiveLocalComputation? (LocalNameTable.mapIds mapping table)
        (Resolved.LocalScope.mapIds mapping context) source =
      elaborateRecursiveLocalComputation? table context source := by
  cases original : elaborateRecursiveLocalComputation? table context source with
  | none =>
      cases renamed : elaborateRecursiveLocalComputation? (LocalNameTable.mapIds mapping table)
          (Resolved.LocalScope.mapIds mapping context) source with
      | none => rfl
      | some result =>
          rcases result with ⟨core, type⟩
          have accepted := elaborateRecursiveLocalComputation?_iff.mpr
            ((recursiveLocalComputationElaborates_mapIds_iff mapping injective).mp
              (elaborateRecursiveLocalComputation?_iff.mp renamed))
          rw [original] at accepted
          cases accepted
  | some result =>
      rcases result with ⟨core, type⟩
      exact elaborateRecursiveLocalComputation?_iff.mpr
        ((recursiveLocalComputationElaborates_mapIds_iff mapping injective).mpr
          (elaborateRecursiveLocalComputation?_iff.mp original))

end Solcore.Frontend
