import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionIndexSource
import Solcore.SourceSemantics.CoreLowering.CompatibleMappingPreparation

/-! Successful index lowering retains the real prepared comparator and exact
child compilation equations. These static receipts contain no child execution. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionIndices
open Core Frontend SourceInference CompatibleExpressionReads CompatibleMapping
open CompatibleEncoding (bind_ok mapError_ok)
abbrev ValuesContext := SourceCoreCompatibleValues.Context
abbrev Scope := SourceCoreLocalCell.Scope
abbrev Child := SourceCoreFunctions.ExpressionLowerer

private theorem ensureType_ok {site : SourceCoreElaboration.ErrorSite} {expected actual : Core.Ty}
    (checked : SourceCoreBasic.ensureType site expected actual = .ok ()) : expected = actual := by
  by_cases same : expected = actual
  · exact same
  · simp [SourceCoreBasic.ensureType, same] at checked

structure Header (values : ValuesContext) (source : TypedSource) (id base : ExpressionId)
    (node baseNode : ExpressionNode) (layout : Core.OrderedMapping.Layout)
    (comparison : SourceCoreCompatibleDataEquality.Prepared values.checked)
    (first second : SourceCoreBasic.LoweredExpr) : Prop where
  metadata : CompatibleExpressionReads.Metadata values.checked source id node layout.valueType
  baseMetadata : CompatibleExpressionReads.Metadata values.checked source base baseNode first.type
  baseType : first.type = SourceCoreMappingWithDefault.type layout
  keyType : second.type = layout.keyType
  registered : layout.Registered values.checked.catalog.definitions
  comparisonType : layout.keyType = comparison.type
  generated : ∃ key value budget,
    SourceCoreRawMetadata.runtimeType baseNode.type = .mapping key value ∧
    values.checked.catalog.mappingLayout key value = .ok layout ∧
    SourceCoreCompatibleDataEquality.prepare budget values.checked key = .ok comparison

theorem index_of_lower {values : ValuesContext} {child : Child} {fuel : Nat} {source : TypedSource} {scope : Scope}
    {id base key : ExpressionId} {node baseNode : ExpressionNode}
    {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (found : source.lookupExpression? id = some node) (baseFound : source.lookupExpression? base = some baseNode)
    (form : node.form = .index base key)
    (accepted : SourceCoreCompatibleDataExpressions.lowerWithReasons (fuel + 1) values child source scope id reasonAt = .ok lowered) :
    ∃ layout comparison first second,
      lowered = ⟨layout.valueType, SourceCoreCompatibleDataExpressions.index layout comparison.expression first.expression second.expression (reasonAt id)⟩ ∧
      Header values source id base node baseNode layout comparison first second ∧
      child fuel source scope base reasonAt = .ok first ∧ child fuel source scope key reasonAt = .ok second := by
  unfold SourceCoreCompatibleDataExpressions.lowerWithReasons at accepted
  obtain ⟨read, readAccepted, accepted⟩ := bind_ok accepted
  rcases read with ⟨actualNode, type⟩
  have metadata := metadata_of_read readAccepted
  have same := Option.some.inj (metadata.found.symm.trans found)
  subst actualNode
  simp only [form] at accepted
  obtain ⟨baseRead, baseAccepted, accepted⟩ := bind_ok accepted
  rcases baseRead with ⟨actualBase, baseType⟩
  have baseMetadata := metadata_of_read baseAccepted
  have same := Option.some.inj (baseMetadata.found.symm.trans baseFound)
  subst actualBase
  cases mappingType : SourceCoreRawMetadata.runtimeType baseNode.type <;>
    simp only [mappingType, pure, Except.pure, bind, Except.bind] at accepted
  all_goals try cases accepted
  rename_i sourceKey sourceValue
  obtain ⟨layout, selected, accepted⟩ := bind_ok accepted
  have selected := mapError_ok selected
  obtain ⟨success, resultEnsured, accepted⟩ := bind_ok accepted
  cases success
  have resultType := ensureType_ok resultEnsured
  obtain ⟨success, baseEnsured, accepted⟩ := bind_ok accepted
  cases success
  have baseTypeEq : baseType = SourceCoreMappingWithDefault.type layout := ensureType_ok baseEnsured
  obtain ⟨first, firstGenerated, accepted⟩ := bind_ok accepted
  obtain ⟨second, secondGenerated, accepted⟩ := bind_ok accepted
  obtain ⟨success, firstEnsured, accepted⟩ := bind_ok accepted
  cases success
  have firstType : baseType = first.type := ensureType_ok firstEnsured
  obtain ⟨success, secondEnsured, accepted⟩ := bind_ok accepted
  cases success
  have secondType := ensureType_ok secondEnsured
  obtain ⟨comparison, comparisonGenerated, accepted⟩ := bind_ok accepted
  have comparisonGenerated := mapError_ok comparisonGenerated
  cases accepted
  have facts := CompatibleEncoding.mappingLayout_facts selected
  have comparisonProjection := comparison.projection
  rw [comparison_sourceType comparisonGenerated] at comparisonProjection
  refine ⟨layout, comparison, first, second, ?_, ?_, firstGenerated, secondGenerated⟩
  · cases resultType; rfl
  · exact ⟨resultType ▸ metadata, firstType ▸ baseMetadata, firstType.symm.trans baseTypeEq,
      secondType.symm, facts.2.2.2, Except.ok.inj (facts.2.1.symm.trans comparisonProjection),
      ⟨sourceKey, sourceValue, fuel, mappingType, selected, comparisonGenerated⟩⟩

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionIndices
