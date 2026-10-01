import Solcore.SourceSemantics.CoreLowering.CompatibleMappingPlaces

/-! Exact equations for a real single-index compatible place preparation.
These static receipts do not assume any getter or setter execution. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleMapping
open Core Frontend SourceInference SourceCoreCompatibleDataPlaces

 theorem comparison_sourceType {checked : Checked} {fuel : Nat} {source : TypeSystem.Ty}
    {prepared : SourceCoreCompatibleDataEquality.Prepared checked}
    (accepted : SourceCoreCompatibleDataEquality.prepare fuel checked source = .ok prepared) : prepared.sourceType = source := by
  unfold SourceCoreCompatibleDataEquality.prepare at accepted
  split at accepted <;> try cases accepted
  split at accepted <;> try cases accepted
  split at accepted <;> try cases accepted
  dsimp only at accepted
  split at accepted <;> cases accepted
  rfl

 def Index.of_generated {checked : Checked} {fuel : Nat} {source : TypeSystem.Ty}
    {prepared : SourceCoreCompatibleDataEquality.Prepared checked} {layout : Core.OrderedMapping.Layout}
    {key : ExpressionId} {position : Nat} {missing : Word}
    (accepted : SourceCoreCompatibleDataEquality.prepare fuel checked source = .ok prepared)
    (projected : checked.catalog.project source = .ok layout.keyType) :
    Index checked ⟨layout, key, position, prepared.expression, missing⟩ where
  comparison := prepared
  expression := rfl
  keyType := by
    have projection := prepared.projection
    rw [comparison_sourceType accepted] at projection
    exact Except.ok.inj (projected.symm.trans projection)

 theorem prepare_single {context : SourceCoreCompatibleDataPlaces.Context} {fuel : Nat} {route : Route} {invalid : Word} {missing : TypeSystem.Ty → Word}
    {layout : Core.OrderedMapping.Layout} {key : ExpressionId} {sourceKey sourceValue recordedValue : TypeSystem.Ty}
    {entry : SourceCoreDataCatalog.Entry} {comparison : SourceCoreCompatibleDataEquality.Prepared context.checked}
    (steps : route.steps = [.index layout key sourceValue])
    (selected : context.checked.catalog.entries[layout.dataType.index]? = some entry)
    (mappingType : entry.sourceType = .mapping sourceKey recordedValue)
    (generated : SourceCoreCompatibleDataEquality.prepare fuel context.checked sourceKey = .ok comparison) :
    prepare context fuel route invalid missing = .ok
      ⟨route, [.index ⟨layout, key, 0, comparison.expression, missing sourceValue⟩], [(key, layout.keyType)], invalid⟩ := by
  simp [prepare, steps, selected, mappingType, generated, bind, Except.bind, pure, Except.pure, Except.mapError]

end Solcore.SourceSemantics.CoreLowering.CompatibleMapping
