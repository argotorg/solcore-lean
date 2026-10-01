import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionIndexTree
import Solcore.SourceSemantics.CoreLowering.CompatiblePayloadRuntimeTypes

/-! Exact index helper syntax and scalar source key guards. The native helper
may allocate administrative closures; all payload metadata remains source-owned. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionIndices
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CompatibleMapping
open CompatibleExpressionPrimitives

private theorem lift_weaken (expression : Expr) (ξ : Renaming) :
    (expression.weakenAt 0).rename ξ.lift = (expression.rename ξ).weakenAt 0 := by
  rw [← Expr.rename_insertion, Expr.rename_comp, Renaming.lift_comp_insertion_zero,
    ← Expr.rename_comp, Expr.rename_insertion]

private theorem lookup_rename {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : SourceCoreCompatibleDataEquality.Prepared checked) {layout : Core.OrderedMapping.Layout}
    (registered : layout.Registered checked.catalog.definitions) (keyType : layout.keyType = prepared.type)
    (reason : Word) (ξ : Renaming) :
    (SourceCoreMappingWithDefault.lookup layout reason prepared.expression (.var 1) (.var 0)).rename ξ.lift.lift =
      SourceCoreMappingWithDefault.lookup layout reason prepared.expression (.var 1) (.var 0) := by
  have comparator := prepared.typed.rename (mapping := Renaming.id)
    (target := [layout.keyType, SourceCoreMappingWithDefault.type layout]) (by intro index type found; cases found)
  simp only [Expr.rename_id] at comparator
  have typed : HasType [layout.keyType, SourceCoreMappingWithDefault.type layout]
      (SourceCoreMappingWithDefault.lookup layout reason prepared.expression (.var 1) (.var 0))
      (LanguageResult.resultType layout.valueType) checked.catalog.definitions := by
    apply SourceCoreMappingWithDefault.lookup_hasType reason registered
    · simpa only [Core.OrderedMapping.Layout.comparisonType, SourceCoreCompatibleDataEquality.comparatorType,
        SourceCoreDataEquality.comparatorType, keyType] using comparator
    · exact .var rfl
    · exact .var rfl
  have same := CoreProof.typed_rename_agree typed (left := ξ.lift.lift) (right := Renaming.id) (by
    intro index bound
    have small : index < 2 := bound
    cases index with
    | zero => rfl
    | succ index => cases index with
      | zero => rfl
      | succ index => omega)
  simpa only [Expr.rename_id] using same

theorem index_rename {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : SourceCoreCompatibleDataEquality.Prepared checked) {layout : Core.OrderedMapping.Layout}
    (registered : layout.Registered checked.catalog.definitions) (keyType : layout.keyType = prepared.type)
    (base key : Expr) (reason : Word) (ξ : Renaming) :
    (SourceCoreCompatibleDataExpressions.index layout prepared.expression base key reason).rename ξ =
      SourceCoreCompatibleDataExpressions.index layout prepared.expression (base.rename ξ) (key.rename ξ) reason := by
  simp only [SourceCoreCompatibleDataExpressions.index, CompatibleMapping.Transport.expression_weaken,
    LanguageResult.bind, Expr.rename, Renaming.lift, lift_weaken]
  exact congrArg (Expr.caseE (base.rename ξ) (.inLeft layout.valueType (.var 0)))
    (congrArg (Expr.caseE ((key.rename ξ).weakenAt 0) (.inLeft layout.valueType (.var 0)))
      (lookup_rename prepared registered keyType reason ξ))

variable {checked : SourceCoreCompatibleCatalog.Checked} {registry : SourceCoreRawMetadata.Registry}
  {ambient : AmbientDefinitions checked.catalog.definitions} {functions : FunctionModel checked.catalog ambient}
  {mapping : LocationMap} {world : StoreTyping}

theorem SourceScalar.runtime_matches {expected raw : TypeSystem.Ty} (scalar : SourceScalar expected)
    {source : Dynamic.Value} {value : Value} {type : Ty}
    (related : ValueRep checked registry functions mapping world expected source value type)
    (view : SourceCoreRawMetadata.runtimeType expected = SourceCoreRawMetadata.runtimeType raw) :
    Dynamic.ValueRuntimeTypeMatches source raw := by
  have projected := related.projection
  cases scalar with
  | bool =>
    cases projected
    obtain ⟨value, rfl, rfl⟩ := bool_fields related
    exact .intro (.bool value) (by simpa only [runtimeType_agrees_metadata] using view)
  | word =>
    cases projected
    obtain ⟨value, rfl, rfl⟩ := word_fields related
    exact .intro (.word value) (by simpa only [runtimeType_agrees_metadata] using view)
  | integer =>
    cases projected
    obtain ⟨value, rfl, rfl⟩ := integer_fields related
    exact .intro (.integer value) (by simpa only [runtimeType_agrees_metadata] using view)

theorem Header.mapping_fields {values : ValuesContext} {source : TypedSource} {id base : ExpressionId}
    {node baseNode keyNode : ExpressionNode} {layout : Core.OrderedMapping.Layout}
    {comparison : SourceCoreCompatibleDataEquality.Prepared values.checked} {first second : SourceCoreBasic.LoweredExpr}
    (header : Header values source id base node baseNode layout comparison first second)
    (sourceType : baseNode.type = .mapping keyNode.type node.type)
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions values.checked.catalog.definitions}
    {functions : FunctionModel values.checked.catalog ambient} {mapping : LocationMap} {world : StoreTyping}
    {sourceKey sourceValue : TypeSystem.Ty} {entries : List (Dynamic.Value × Dynamic.Value)} {value : Value}
    (represented : ValueRep values.checked registry functions mapping world baseNode.type
      (.mapping sourceKey sourceValue entries) value first.type) :
    ∃ tag nativeEntries fallback,
      value = Transport.carrier tag fallback layout nativeEntries ∧
      SourceCoreRawMetadata.runtimeType keyNode.type = SourceCoreRawMetadata.runtimeType sourceKey ∧
      SourceCoreRawMetadata.runtimeType node.type = SourceCoreRawMetadata.runtimeType sourceValue ∧
      Fields values.checked registry functions mapping world sourceKey sourceValue entries tag layout nativeEntries fallback := by
  obtain ⟨tag, actual, nativeEntries, fallback, valueEq, typeEq, view, fields⟩ := CompatibleMapping.mapping_fields represented rfl
  have same := registered_layout_eq fields.registered header.registered (typeEq.symm.trans header.baseType)
  subst actual
  rw [sourceType] at view
  have views := TypeSystem.Ty.mapping.inj view
  exact ⟨tag, nativeEntries, fallback, valueEq, views.1, views.2, fields⟩

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionIndices
