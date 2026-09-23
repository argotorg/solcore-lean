import Solcore.Frontend.LocalName
import Solcore.Frontend.LocalExpression
import Solcore.Resolved.Renaming
import Solcore.Frontend.LocalExpressionTyping
import Solcore.Frontend.LocalExpressionEvaluation

/-! Local-expression renaming and its semantic correspondence. -/

/-!
## Consolidated module: `Solcore.Frontend.LocalExpressionRenamingProperties`
-/

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
  | unit => exact .unit
  | identifier found =>
      exact .identifier ((LocalNameTable.lookup_mapIds_iff_exists mapping).mpr ⟨_, found, rfl⟩)
  | wordLiteral meaning => exact .wordLiteral meaning
  | group _ ih => exact .group ih
  | pair _ _ leftIH rightIH => exact .pair leftIH rightIH
  | many _ _ headIH tailIH => exact .many headIH tailIH
  | logicalNot _ ih => exact .logicalNot ih
  | bitNot _ ih => exact .bitNot ih
  | add _ _ leftIH rightIH => exact .add leftIH rightIH
  | subtract _ _ leftIH rightIH => exact .subtract leftIH rightIH
  | multiply _ _ leftIH rightIH => exact .multiply leftIH rightIH
  | divide _ _ leftIH rightIH => exact .divide leftIH rightIH
  | modulo _ _ leftIH rightIH => exact .modulo leftIH rightIH
  | greater _ _ leftIH rightIH => exact .greater leftIH rightIH
  | equal _ _ leftIH rightIH => exact .equal leftIH rightIH
  | notEqual _ _ leftIH rightIH => exact .notEqual leftIH rightIH
  | lessEqual _ _ leftIH rightIH => exact .lessEqual leftIH rightIH
  | less _ _ leftIH rightIH => exact .less leftIH rightIH
  | greaterEqual _ _ leftIH rightIH => exact .greaterEqual leftIH rightIH
  | bitAnd _ _ leftIH rightIH => exact .bitAnd leftIH rightIH
  | bitOr _ _ leftIH rightIH => exact .bitOr leftIH rightIH
  | bitXor _ _ leftIH rightIH => exact .bitXor leftIH rightIH
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
    | unit => exact ⟨.unit, .unit, rfl⟩
    | identifier found =>
        obtain ⟨original, originalFound, rfl⟩ :=
          (LocalNameTable.lookup_mapIds_iff_exists mapping).mp found
        exact ⟨.var original, .identifier originalFound, rfl⟩
    | wordLiteral meaning => exact ⟨_, .wordLiteral meaning, rfl⟩
    | group _ ih =>
        obtain ⟨original, child, rfl⟩ := ih
        exact ⟨original, .group child, rfl⟩
    | pair _ _ leftIH rightIH =>
        obtain ⟨originalLeft, leftChild, rfl⟩ := leftIH
        obtain ⟨originalRight, rightChild, rfl⟩ := rightIH
        exact ⟨.pair originalLeft originalRight, .pair leftChild rightChild, rfl⟩
    | many _ _ headIH tailIH =>
        obtain ⟨originalHead, headChild, rfl⟩ := headIH
        obtain ⟨originalTail, tailChild, rfl⟩ := tailIH
        exact ⟨.pair originalHead originalTail, .many headChild tailChild, rfl⟩
    | logicalNot _ ih =>
        obtain ⟨original, child, rfl⟩ := ih
        exact ⟨.unary .boolNot original, .logicalNot child, rfl⟩
    | bitNot _ ih =>
        obtain ⟨original, child, rfl⟩ := ih
        exact ⟨.unary .wordNot original, .bitNot child, rfl⟩
    | add _ _ leftIH rightIH =>
        obtain ⟨originalLeft, leftChild, rfl⟩ := leftIH
        obtain ⟨originalRight, rightChild, rfl⟩ := rightIH
        exact ⟨.binary .wordAdd originalLeft originalRight, .add leftChild rightChild, rfl⟩
    | subtract _ _ leftIH rightIH =>
        obtain ⟨originalLeft, leftChild, rfl⟩ := leftIH
        obtain ⟨originalRight, rightChild, rfl⟩ := rightIH
        exact ⟨.binary .wordSub originalLeft originalRight, .subtract leftChild rightChild, rfl⟩
    | multiply _ _ leftIH rightIH =>
        obtain ⟨originalLeft, leftChild, rfl⟩ := leftIH
        obtain ⟨originalRight, rightChild, rfl⟩ := rightIH
        exact ⟨.binary .wordMul originalLeft originalRight, .multiply leftChild rightChild, rfl⟩
    | divide _ _ leftIH rightIH =>
        obtain ⟨originalLeft, leftChild, rfl⟩ := leftIH
        obtain ⟨originalRight, rightChild, rfl⟩ := rightIH
        exact ⟨.binary .wordDiv originalLeft originalRight, .divide leftChild rightChild, rfl⟩
    | modulo _ _ leftIH rightIH =>
        obtain ⟨originalLeft, leftChild, rfl⟩ := leftIH
        obtain ⟨originalRight, rightChild, rfl⟩ := rightIH
        exact ⟨.binary .wordMod originalLeft originalRight, .modulo leftChild rightChild, rfl⟩
    | greater _ _ leftIH rightIH =>
        obtain ⟨originalLeft, leftChild, rfl⟩ := leftIH
        obtain ⟨originalRight, rightChild, rfl⟩ := rightIH
        exact ⟨.binary .wordGt originalLeft originalRight, .greater leftChild rightChild, rfl⟩
    | equal _ _ leftIH rightIH =>
        obtain ⟨originalLeft, leftChild, rfl⟩ := leftIH
        obtain ⟨originalRight, rightChild, rfl⟩ := rightIH
        exact ⟨.binary .wordEq originalLeft originalRight, .equal leftChild rightChild, rfl⟩
    | notEqual _ _ leftIH rightIH =>
        obtain ⟨originalLeft, leftChild, rfl⟩ := leftIH
        obtain ⟨originalRight, rightChild, rfl⟩ := rightIH
        exact ⟨.unary .boolNot (.binary .wordEq originalLeft originalRight), .notEqual leftChild rightChild, rfl⟩
    | lessEqual _ _ leftIH rightIH =>
        obtain ⟨originalLeft, leftChild, rfl⟩ := leftIH
        obtain ⟨originalRight, rightChild, rfl⟩ := rightIH
        exact ⟨.unary .boolNot (.binary .wordGt originalLeft originalRight), .lessEqual leftChild rightChild, rfl⟩
    | less _ _ leftIH rightIH =>
        obtain ⟨originalLeft, leftChild, rfl⟩ := leftIH
        obtain ⟨originalRight, rightChild, rfl⟩ := rightIH
        exact ⟨.wordLt originalLeft originalRight, .less leftChild rightChild, rfl⟩
    | greaterEqual _ _ leftIH rightIH =>
        obtain ⟨originalLeft, leftChild, rfl⟩ := leftIH
        obtain ⟨originalRight, rightChild, rfl⟩ := rightIH
        exact ⟨.unary .boolNot (.wordLt originalLeft originalRight),
          .greaterEqual leftChild rightChild, rfl⟩
    | bitAnd _ _ leftIH rightIH =>
        obtain ⟨originalLeft, leftChild, rfl⟩ := leftIH
        obtain ⟨originalRight, rightChild, rfl⟩ := rightIH
        exact ⟨.binary .wordAnd originalLeft originalRight, .bitAnd leftChild rightChild, rfl⟩
    | bitOr _ _ leftIH rightIH =>
        obtain ⟨originalLeft, leftChild, rfl⟩ := leftIH
        obtain ⟨originalRight, rightChild, rfl⟩ := rightIH
        exact ⟨.binary .wordOr originalLeft originalRight, .bitOr leftChild rightChild, rfl⟩
    | bitXor _ _ leftIH rightIH =>
        obtain ⟨originalLeft, leftChild, rfl⟩ := leftIH
        obtain ⟨originalRight, rightChild, rfl⟩ := rightIH
        exact ⟨.binary .wordXor originalLeft originalRight, .bitXor leftChild rightChild, rfl⟩
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

/-!
## Consolidated module: `Solcore.Frontend.LocalExpressionRenamingSemantics`
-/

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
    | unit => exact .unit
    | identifier named found =>
        obtain ⟨id, oldNamed, same⟩ := (LocalNameTable.lookup_mapIds_iff_exists mapping).mp named
        rw [← same] at found
        exact .identifier oldNamed ((Resolved.LocalScope.lookup_mapIds_iff mapping injective).mp found)
    | wordLiteral meaning => exact .wordLiteral meaning
    | group _ ih => exact .group ih
    | pair _ _ leftIH rightIH => exact .pair leftIH rightIH
    | many _ _ headIH tailIH => exact .many headIH tailIH
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
    | unit => exact .unit
    | identifier named found =>
        exact .identifier ((LocalNameTable.lookup_mapIds_iff mapping injective).mpr named)
          ((Resolved.LocalScope.lookup_mapIds_iff mapping injective).mpr found)
    | wordLiteral meaning => exact .wordLiteral meaning
    | group _ ih => exact .group ih
    | pair _ _ leftIH rightIH => exact .pair leftIH rightIH
    | many _ _ headIH tailIH => exact .many headIH tailIH
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
