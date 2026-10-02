import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionDataLeafNativeTyping

/-! Actual proxy lowering needs no child-code typing. Mapping reads supply
index operands without a scalar-key restriction; the exact prepared comparator
and registered layout determine the native operation. -/
set_option autoImplicit false
namespace Tests.SourceCoreDataLeafNativeTyping
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open CompatibleExpressionScalarNativeTyping CompatibleExpressionDataLeafNativeTyping

theorem actual_proxy_native
    {values : SourceCoreCompatibleValues.Context} {child : SourceCoreFunctions.ExpressionLowerer}
    {fuel : Nat} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {id : ExpressionId} {node : ExpressionNode} {inner : TypeSystem.Ty}
    {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (found : source.lookupExpression? id = some node) (form : node.form = .proxy inner)
    (accepted : SourceCoreCompatibleDataExpressions.lowerWithReasons (fuel + 1) values child source scope id reasonAt = .ok lowered)
    (context : Core.Context) {definitions : DataEnvironment}
    (extension : values.checked.catalog.definitions.Extends definitions) : NativeTyping definitions context lowered := by
  obtain ⟨owner, header, rfl, receipt⟩ := CompatibleExpressionProxies.proxy_of_lower found form accepted
  exact proxy_native_at (scope := scope) (.proxy receipt) context extension

/-- The checked read certificates close both operands. Compound raw mapping
keys, lazy mapping defaults and arbitrary administrative slots are admitted. -/
theorem actual_reads_index_native
    {fuel : Nat} {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {sourceContext : SourceSemantics.Context}
    {id base key : ExpressionId} {node baseNode : ExpressionNode}
    {layout : Core.OrderedMapping.Layout}
    {comparison : SourceCoreCompatibleDataEquality.Prepared values.checked}
    {first second : SourceCoreBasic.LoweredExpr} {reasonAt : ExpressionId → Word}
    (receipt : CompatibleExpressionIndices.Header values source id base node baseNode layout comparison first second)
    (baseRead : CompatibleExpressionReads.LoweredRead fuel values source sourceContext reasonAt scope base first)
    (keyRead : CompatibleExpressionReads.LoweredRead fuel values source sourceContext reasonAt scope key second)
    (visibleTypes : ScopeWellFormed values.checked.catalog.definitions scope)
    (administrative : Core.Context) {definitions : DataEnvironment}
    (extension : values.checked.catalog.definitions.Extends definitions) :
    NativeTyping definitions (SourceCoreLocalCell.coreContext scope ++ administrative)
      ⟨layout.valueType, SourceCoreCompatibleDataExpressions.index layout comparison.expression
        first.expression second.expression (reasonAt id)⟩ := by
  obtain ⟨baseWF, baseTyped⟩ := read_native baseRead visibleTypes administrative
  obtain ⟨keyWF, keyTyped⟩ := read_native keyRead visibleTypes administrative
  exact index_native_at receipt
    ⟨baseWF.extend_definitions extension, baseTyped.extend_definitions extension⟩
    ⟨keyWF.extend_definitions extension, keyTyped.extend_definitions extension⟩ (reasonAt id) extension

/-- Ambient child code may itself mention appended frame definitions. It is
never required to type-check under the smaller base catalog. -/
theorem ambient_index_native
    {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
    {id base : ExpressionId} {node baseNode : ExpressionNode} {layout : Core.OrderedMapping.Layout}
    {comparison : SourceCoreCompatibleDataEquality.Prepared values.checked}
    {first second : SourceCoreBasic.LoweredExpr} {context : Core.Context} {definitions : DataEnvironment}
    (receipt : CompatibleExpressionIndices.Header values source id base node baseNode layout comparison first second)
    (baseTyped : NativeTyping definitions context first)
    (keyTyped : NativeTyping definitions context second)
    (reason : Word) (extension : values.checked.catalog.definitions.Extends definitions) :
    NativeTyping definitions context
      ⟨layout.valueType, SourceCoreCompatibleDataExpressions.index layout comparison.expression
        first.expression second.expression reason⟩ :=
  index_native_at receipt baseTyped keyTyped reason extension

end Tests.SourceCoreDataLeafNativeTyping
