import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionScalarNativeTyping
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionProxyCertificates
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionIndexCertificates

/-! Production data leaves use their exact registered layouts and comparator.
Proxy typing needs no child receipt. Index typing consumes the enclosing
structural induction's actual base and key code, including compound keys. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionDataLeafNativeTyping
open Core Frontend SourceInference
open CompatibleExpressionScalarNativeTyping

theorem proxy_native {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : CompatibleExpressionProxies.Certificate values source scope id lowered)
    (context : Core.Context) : NativeTyping values.checked.catalog.definitions context lowered := by
  cases receipt with
  | proxy header =>
    obtain ⟨_, registered⟩ := DataEnvironment.lookupConstructorPayloadType?_owner header.registered
    exact ⟨.namedData registered, LanguageResult.success_hasType (.construct header.registered .word)⟩

private theorem closed_native {definitions : DataEnvironment} {code : Expr} {type : Ty}
    (typed : HasType [] code type definitions) (context : Core.Context) : HasType context code type definitions := by
  have extended := typed.rename (mapping := Renaming.id) (target := context)
    (by intro index type found; cases found)
  simpa using extended

/-- The real prepared comparator is checked in an empty context and is then
transported statically. No runtime closure weakening is assumed. -/
theorem index_native {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
    {id base : ExpressionId} {node baseNode : ExpressionNode} {layout : Core.OrderedMapping.Layout}
    {comparison : SourceCoreCompatibleDataEquality.Prepared values.checked}
    {first second : SourceCoreBasic.LoweredExpr} {context : Core.Context}
    (receipt : CompatibleExpressionIndices.Header values source id base node baseNode layout comparison first second)
    (baseTyped : NativeTyping values.checked.catalog.definitions context first)
    (keyTyped : NativeTyping values.checked.catalog.definitions context second)
    (reason : Word) :
    NativeTyping values.checked.catalog.definitions context
      ⟨layout.valueType, SourceCoreCompatibleDataExpressions.index layout comparison.expression
        first.expression second.expression reason⟩ := by
  refine ⟨receipt.registered.valueWellFormed, SourceCoreCompatibleDataExpressions.index_hasType reason
    receipt.registered ?_ ?_ ?_⟩
  · simpa only [receipt.comparisonType, SourceCoreCompatibleDataEquality.comparatorType,
      SourceCoreDataEquality.comparatorType] using closed_native comparison.typed context
  · simpa only [receipt.baseType] using baseTyped.2
  · simpa only [receipt.keyType] using keyTyped.2

theorem proxy_native_at {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : CompatibleExpressionProxies.Certificate values source scope id lowered)
    (context : Core.Context) {definitions : DataEnvironment}
    (extension : values.checked.catalog.definitions.Extends definitions) : NativeTyping definitions context lowered := by
  obtain ⟨wellFormed, native⟩ := proxy_native receipt context
  exact ⟨wellFormed.extend_definitions extension, native.extend_definitions extension⟩

theorem index_native_at {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
    {id base : ExpressionId} {node baseNode : ExpressionNode} {layout : Core.OrderedMapping.Layout}
    {comparison : SourceCoreCompatibleDataEquality.Prepared values.checked}
    {first second : SourceCoreBasic.LoweredExpr} {context : Core.Context} {definitions : DataEnvironment}
    (receipt : CompatibleExpressionIndices.Header values source id base node baseNode layout comparison first second)
    (baseTyped : NativeTyping definitions context first)
    (keyTyped : NativeTyping definitions context second)
    (reason : Word)
    (extension : values.checked.catalog.definitions.Extends definitions) :
    NativeTyping definitions context
      ⟨layout.valueType, SourceCoreCompatibleDataExpressions.index layout comparison.expression
        first.expression second.expression reason⟩ := by
  have registered := receipt.registered.extend_definitions extension
  refine ⟨registered.valueWellFormed, SourceCoreCompatibleDataExpressions.index_hasType reason
    registered ?_ ?_ ?_⟩
  · simpa only [receipt.comparisonType, SourceCoreCompatibleDataEquality.comparatorType,
      SourceCoreDataEquality.comparatorType] using closed_native (comparison.typed.extend_definitions extension) context
  · simpa only [receipt.baseType] using baseTyped.2
  · simpa only [receipt.keyType] using keyTyped.2

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionDataLeafNativeTyping
