import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionIndexCertificates
import Solcore.SourceSemantics.CoreLowering.CompatibleMappingView

/-! The unavailable mapping branch retains its actual raw Fields,
metadata header and Source runtime views. Source index occurrence membership
is supplied by the real upper Tree constructor, not recovered from layout. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionIndices
open Core Frontend SourceInference GeneralHeap CompatiblePayload CompatibleMapping

/-- This receipt is constructed only at the actual unavailable lookup branch.
It keeps the whole raw mapping representation and exact absent key. -/
structure MissingWitness {values : ValuesContext} {source : TypedSource}
    {id base : ExpressionId} {node baseNode keyNode : ExpressionNode}
    {layout : Core.OrderedMapping.Layout}
    {comparison : SourceCoreCompatibleDataEquality.Prepared values.checked}
    {first second : SourceCoreBasic.LoweredExpr}
    (header : Header values source id base node baseNode layout comparison first second)
    {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions values.checked.catalog.definitions}
    (functions : FunctionModel values.checked.catalog ambient)
    (mapping : LocationMap) (world : StoreTyping)
    (baseSource keySource : Dynamic.Value) (baseValue : Value)
    (rawKey rawValue : TypeSystem.Ty) (sources : List (Dynamic.Value × Dynamic.Value))
    (tag : Word) (entries : Core.OrderedMapping.Entries) (fallback : Option Value) : Prop where
  contains : ContainsExpression source id node
  baseContains : ContainsExpression source base baseNode
  sourceType : baseNode.type = .mapping keyNode.type node.type
  baseShape : baseSource = .mapping rawKey rawValue sources
  nativeShape : baseValue = Transport.carrier tag fallback layout entries
  keyView : SourceCoreRawMetadata.runtimeType keyNode.type = SourceCoreRawMetadata.runtimeType rawKey
  valueView : SourceCoreRawMetadata.runtimeType node.type = SourceCoreRawMetadata.runtimeType rawValue
  fields : Fields values.checked registry functions mapping world rawKey rawValue sources tag layout entries fallback
  keyTyped : Dynamic.ValueRuntimeTypeMatches keySource rawKey
  absent : Dynamic.MappingAbsent keySource sources
  unavailable : ¬ Dynamic.Defaultable rawValue

/-- This policy is called with the Fields extracted from the actual represented
mapping. It asks for no relation on unrelated registered mapping types. -/
def MissingPolicy {values : ValuesContext} {source : TypedSource}
    {id base : ExpressionId} {node baseNode keyNode : ExpressionNode}
    {layout : Core.OrderedMapping.Layout}
    {comparison : SourceCoreCompatibleDataEquality.Prepared values.checked}
    {first second : SourceCoreBasic.LoweredExpr}
    (header : Header values source id base node baseNode layout comparison first second)
    {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions values.checked.catalog.definitions}
    (functions : FunctionModel values.checked.catalog ambient)
    (mapping : LocationMap) (world : StoreTyping)
    (baseSource keySource : Dynamic.Value) (baseValue : Value)
    (reason : Word) (faults : Dynamic.SemanticFault → Word → Prop) : Prop :=
  ∀ rawKey rawValue sources tag entries fallback,
    MissingWitness (keyNode := keyNode) (registry := registry) header functions mapping world baseSource keySource baseValue
      rawKey rawValue sources tag entries fallback →
    faults (.missingMappingDefault rawValue) (reason.add tag)

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionIndices
