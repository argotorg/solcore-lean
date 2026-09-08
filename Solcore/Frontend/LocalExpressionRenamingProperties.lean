import Solcore.Frontend.LocalNameRenaming
import Solcore.Frontend.LocalExpressionResolutionProperties
import Solcore.Resolved.Renaming

/-! Resolution commutes with arbitrary identity maps. The source tree, including
all spellings and ranges, is unchanged. Unlike context/environment lookup,
name-based resolution does not require the map to be injective. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem ResolvesLocalExpression.mapIds {table : LocalNameTable}
    {source : Syntax.Expr} {resolved : Resolved.Expr}
    (resolution : ResolvesLocalExpression table source resolved)
    (mapping : Resolved.LocalId → Resolved.LocalId) :
    ResolvesLocalExpression (LocalNameTable.mapIds mapping table) source
      (resolved.renameIds mapping) := by
  induction resolution with
  | identifier found =>
      exact .identifier ((LocalNameTable.lookup_mapIds_iff_exists mapping).mpr ⟨_, found, rfl⟩)
  | group _ ih => exact .group ih
  | logicalNot _ ih => exact .logicalNot ih
  | logicalAnd _ _ leftIH rightIH => exact .logicalAnd leftIH rightIH
  | logicalOr _ _ leftIH rightIH => exact .logicalOr leftIH rightIH
  | conditional _ _ _ conditionIH thenIH elseIH => exact .conditional conditionIH thenIH elseIH

/-- Every renamed derivation has an original derivation, without choosing an
inverse map or assuming that distinct IDs remain distinct. -/
theorem resolvesLocalExpression_mapIds_iff_exists (mapping : Resolved.LocalId → Resolved.LocalId)
    {table : LocalNameTable} {source : Syntax.Expr} {renamed : Resolved.Expr} :
    ResolvesLocalExpression (LocalNameTable.mapIds mapping table) source renamed ↔
      ∃ original, ResolvesLocalExpression table source original ∧
        original.renameIds mapping = renamed := by
  constructor
  · intro resolution
    induction resolution with
    | identifier found =>
        obtain ⟨original, originalFound, rfl⟩ :=
          (LocalNameTable.lookup_mapIds_iff_exists mapping).mp found
        exact ⟨.var original, .identifier originalFound, rfl⟩
    | group _ ih =>
        obtain ⟨original, child, rfl⟩ := ih
        exact ⟨original, .group child, rfl⟩
    | logicalNot _ ih =>
        obtain ⟨original, child, rfl⟩ := ih
        exact ⟨.unary .boolNot original, .logicalNot child, rfl⟩
    | logicalAnd _ _ leftIH rightIH =>
        obtain ⟨originalLeft, leftChild, rfl⟩ := leftIH
        obtain ⟨originalRight, rightChild, rfl⟩ := rightIH
        exact ⟨.ifE originalLeft originalRight (.bool false), .logicalAnd leftChild rightChild, rfl⟩
    | logicalOr _ _ leftIH rightIH =>
        obtain ⟨originalLeft, leftChild, rfl⟩ := leftIH
        obtain ⟨originalRight, rightChild, rfl⟩ := rightIH
        exact ⟨.ifE originalLeft (.bool true) originalRight, .logicalOr leftChild rightChild, rfl⟩
    | conditional _ _ _ conditionIH thenIH elseIH =>
        obtain ⟨originalCondition, conditionChild, rfl⟩ := conditionIH
        obtain ⟨originalThen, thenChild, rfl⟩ := thenIH
        obtain ⟨originalElse, elseChild, rfl⟩ := elseIH
        exact ⟨.ifE originalCondition originalThen originalElse,
          .conditional conditionChild thenChild elseChild, rfl⟩
  · rintro ⟨original, resolution, rfl⟩
    exact resolution.mapIds mapping

/-- Exact optional commutation includes all unsupported or unmapped source
trees; it does not silently assume whole-expression resolution succeeds. -/
theorem resolveLocalExpression?_mapIds (mapping : Resolved.LocalId → Resolved.LocalId)
    (table : LocalNameTable) (source : Syntax.Expr) :
    resolveLocalExpression? (LocalNameTable.mapIds mapping table) source =
      (resolveLocalExpression? table source).map (Resolved.Expr.renameIds mapping) := by
  cases originalResult : resolveLocalExpression? table source with
  | none =>
      cases renamedResult : resolveLocalExpression? (LocalNameTable.mapIds mapping table) source with
      | none => rfl
      | some renamed =>
          obtain ⟨original, resolution, _⟩ :=
            (resolvesLocalExpression_mapIds_iff_exists mapping).mp
              (resolveLocalExpression?_sound renamedResult)
          have impossible := resolution.complete
          rw [originalResult] at impossible
          cases impossible
  | some original =>
      exact ((resolveLocalExpression?_sound originalResult).mapIds mapping).complete

end Solcore.Frontend
