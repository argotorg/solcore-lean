import Solcore.SourceSemantics.CoreLowering.CompatibleMappingMeaning
import Solcore.SourceSemantics.CoreLowering.CompatibleEncoding

/-! Actual public encoder receipts supply the value-level lookup theorem.
Registered layouts authenticate the omitted key type in the outer carrier;
no equality of native mapping carrier types is treated as a full layout cast. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleMapping
open Core Frontend CompatiblePayload CompatibleEquality DataEquality

 theorem registered_layout_eq {definitions : DataEnvironment} {left right : Core.OrderedMapping.Layout}
    (a : left.Registered definitions) (b : right.Registered definitions)
    (type : SourceCoreMappingWithDefault.type left = SourceCoreMappingWithDefault.type right) : left = right := by
  have parts : left.valueType = right.valueType ∧ left.dataType = right.dataType := by
    simpa [SourceCoreMappingWithDefault.type, Core.OrderedMapping.Layout.lookupResult, Core.OrderedMapping.Layout.type] using type
  have definitions := a.lookup.symm.trans (parts.2 ▸ b.lookup)
  have key : left.keyType = right.keyType := by
    have payloads := congrArg DataDefinition.constructorPayloadTypes (Option.some.inj definitions)
    simp only [Core.OrderedMapping.Layout.definition, List.cons.injEq, Ty.product.injEq, and_true] at payloads
    exact payloads.2.1.1
  cases left; cases right
  simp_all

 theorem encoded_lookup_run {fuel : Nat} {context : SourceCoreCompatibleValues.Context}
    (comparison : SourceCoreCompatibleDataEquality.Prepared context.checked) (layout : Core.OrderedMapping.Layout)
    (registered : layout.Registered context.checked.catalog.definitions) (keyType : layout.keyType = comparison.type)
    {sourceKey sourceValue : TypeSystem.Ty}
    (mappingProjection : context.checked.catalog.project (.mapping sourceKey sourceValue) = .ok (SourceCoreMappingWithDefault.type layout))
    (keyProjection : context.checked.catalog.project sourceKey = .ok layout.keyType)
    {carrier : SourceCoreDataValues.Value} {sources : List (Dynamic.Value × Dynamic.Value)}
    {keyCarrier : SourceCoreDataValues.Value} {sourceLookup : Dynamic.Value}
    {encodedMapping : SourceCoreCompatibleValues.Encoded fuel context (.mapping sourceKey sourceValue) carrier}
    {encodedKey : SourceCoreCompatibleValues.Encoded fuel encodedMapping.context sourceKey keyCarrier}
    (mappingAccepted : SourceCoreCompatibleValues.encode fuel context (.mapping sourceKey sourceValue) carrier = .ok encodedMapping)
    (keyAccepted : SourceCoreCompatibleValues.encode fuel encodedMapping.context sourceKey keyCarrier = .ok encodedKey)
    (mappingMeaning : CompatibleEncoding.Means carrier (.mapping sourceKey sourceValue sources))
    (keyMeaning : CompatibleEncoding.Means keyCarrier sourceLookup)
    {functions : FunctionModel context.checked.catalog} {identities : Dynamic.Value → Word → Prop}
    (faithful : IdentityFaithful identities) (functionLeaves : FunctionObservations context.checked.catalog functions identities)
    (mapping : GeneralHeap.LocationMap) (world : StoreTyping) (environment : Environment) (store : Store) (missingBase : Word)
    (mappingExpression keyExpression : Expr)
    (mappingSelected : Selects environment mappingExpression encodedMapping.value)
    (keySelected : Selects environment keyExpression encodedKey.value) :
    ∃ header result finalStore,
      MetadataRep encodedKey.context.registry (.mapping sourceKey sourceValue) header ∧
      ReadResult context.checked encodedKey.context.registry functions mapping world sourceValue sourceLookup sources layout.valueType missingBase header result ∧
      (∃ required, ∀ budget, required ≤ budget → runStateful budget
        (.initial (SourceCoreMappingWithDefault.lookup layout missingBase comparison.expression mappingExpression keyExpression) environment store) = .done result finalStore) ∧
      (∀ budget actual actualStore, runStateful budget
        (.initial (SourceCoreMappingWithDefault.lookup layout missingBase comparison.expression mappingExpression keyExpression) environment store) = .done actual actualStore →
          actual = result ∧ actualStore = finalStore) ∧
      ∃ administrative, finalStore = store ++ administrative ∧ administrative.length = context.checked.catalog.entries.length + 1 := by
  have represented := CompatibleEncoding.encode_represents_at (functions := functions) mappingAccepted mappingMeaning mapping world
  have represented := represented.extend encodedKey.preserves (.refl mapping) (.refl world)
  have keyRep := CompatibleEncoding.encode_represents_at (context := encodedMapping.context) (functions := functions) keyAccepted keyMeaning mapping world
  have mappingType := Except.ok.inj (encodedMapping.projected.symm.trans mappingProjection)
  have nativeKeyType := Except.ok.inj (encodedKey.projected.symm.trans keyProjection)
  rw [nativeKeyType] at keyRep
  obtain ⟨header, actualLayout, entries, fallback, value, type, _, fields⟩ := mapping_fields represented rfl
  have same := registered_layout_eq fields.registered registered (type.symm.trans mappingType)
  subst actualLayout
  obtain ⟨result, meaning, completes, reflects⟩ := lookup_run comparison keyType faithful functionLeaves fields keyRep
    environment store missingBase mappingExpression keyExpression (by simpa only [value] using mappingSelected) keySelected
  exact ⟨header, result, _, fields.metadata, meaning, completes, reflects,
    Transport.lookupStore_extension comparison layout environment store header fallback entries encodedKey.value⟩

end Solcore.SourceSemantics.CoreLowering.CompatibleMapping
