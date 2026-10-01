import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionIndexCertificates

/-! Index chains over the certified member fragment. Original scalar key
metadata and raw mapping result types remain explicit static facts. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionIndices
open Core Frontend SourceInference

inductive Syntax (source : TypedSource) : ExpressionId → Prop where
  | fragment {id} (tree : CompatibleExpressionMembers.Syntax source id) : Syntax source id
  | index {id node base key keyNode} (found : source.lookupExpression? id = some node)
      (form : node.form = .index base key) (keyFound : source.lookupExpression? key = some keyNode)
      (scalar : SourceScalar keyNode.type) (first : Syntax source base) (second : Syntax source key) : Syntax source id

inductive Tree (fuel : Nat) (values : ValuesContext) (source : TypedSource)
    (context : SourceSemantics.Context) (solved : List SolvedRequirement)
    (reasonAt : ExpressionId → Word) (scope : Scope) :
    ExpressionId → SourceCoreBasic.LoweredExpr → Prop where
  | fragment {id lowered}
      (tree : CompatibleExpressionMembers.Tree fuel values source context solved reasonAt scope id lowered) :
      Tree fuel values source context solved reasonAt scope id lowered
  | index {id node base key baseNode keyNode layout comparison first second}
      (header : Header values source id base node baseNode layout comparison first second)
      (keyFound : source.lookupExpression? key = some keyNode)
      (form : node.form = .index base key)
      (sourceType : baseNode.type = .mapping keyNode.type node.type)
      (scalar : SourceScalar keyNode.type)
      (firstTree : Tree fuel values source context solved reasonAt scope base first)
      (secondTree : Tree fuel values source context solved reasonAt scope key second) :
      Tree fuel values source context solved reasonAt scope id
        ⟨layout.valueType, SourceCoreCompatibleDataExpressions.index layout comparison.expression first.expression second.expression (reasonAt id)⟩

theorem Header.scalar {values : ValuesContext} {source : TypedSource} {id base : ExpressionId}
    {node baseNode keyNode : ExpressionNode} {layout : Core.OrderedMapping.Layout}
    {comparison : SourceCoreCompatibleDataEquality.Prepared values.checked} {first second : SourceCoreBasic.LoweredExpr}
    (header : Header values source id base node baseNode layout comparison first second)
    (sourceType : baseNode.type = .mapping keyNode.type node.type) (scalar : SourceScalar keyNode.type) : Scalar layout.keyType := by
  obtain ⟨key, value, fuel, view, selected, generated⟩ := header.generated
  rw [sourceType] at view
  have shape : SourceCoreRawMetadata.runtimeType keyNode.type = key := (TypeSystem.Ty.mapping.inj view).1
  have projected := (CompatibleEncoding.mappingLayout_facts selected).2.1
  rw [← shape, SourceCoreCompatibleCatalog.Catalog.project_runtimeType] at projected
  exact scalar.projected projected

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionIndices
