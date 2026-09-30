import Solcore.SourceSemantics.CoreLowering.DataPayload
import Solcore.SourceSemantics.CoreLowering.DataDefaults

/-! Static catalog layout receipts used by complete payload representations.
A `Checked` catalog only proves Core definition well-formedness. It does not
by itself prove the source mapping/proxy layout equations below. These are
compile-time data-layout facts, not premises about executing helper code. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataPayload
open Core Frontend Frontend.SourceInference GeneralHeap DataPatternValues

structure CatalogLayouts (catalog : SourceCoreDataCatalog.Catalog) : Prop where
  proxy : ∀ {inner id}, catalog.identity? (.proxy inner) = some id →
    catalog.definitions.lookupConstructorPayloadType? ⟨id, 0⟩ = some .unit
  mapping : ∀ {key value id}, catalog.identity? (.mapping key value) = some id →
    ∃ keyType valueType,
      catalog.project key = .ok keyType ∧ catalog.project value = .ok valueType ∧
      (Core.OrderedMapping.Layout.mk keyType valueType id).Registered catalog.definitions

/-- Actual default-generation certificates produce complete payloads. The
empty mapping still authenticates its declared key/value layout, even though
there are no entries whose values could expose a malformed declaration. -/
theorem default_represents {catalog : SourceCoreDataCatalog.Catalog} {signatures : ProgramSignatures}
    {functions : GenericHeap.PayloadModel catalog} {mapping : LocationMap} {world : StoreTyping}
    (layouts : CatalogLayouts catalog) {sourceType : TypeSystem.Ty} {source : Dynamic.Value}
    {value : Value} {expression : Expr} (tree : DataDefaults.Tree catalog sourceType source value expression) :
    ∃ type, ValueRep catalog signatures functions mapping world sourceType source value type := by
  induction tree with
  | unit => exact ⟨_, .unit⟩
  | bool => exact ⟨_, .bool _⟩
  | word => exact ⟨_, .word _⟩
  | integer => exact ⟨_, .integer _⟩
  | product _ _ left right =>
    obtain ⟨a, first⟩ := left
    obtain ⟨b, second⟩ := right
    exact ⟨_, .product first second⟩
  | proxy inner id identity => exact ⟨_, .proxy identity (layouts.proxy identity)⟩
  | mapping key value id identity =>
    obtain ⟨keyType, valueType, keyProjection, valueProjection, registered⟩ := layouts.mapping identity
    exact ⟨_, .mapping identity keyProjection valueProjection registered (.empty _ _ _ _)⟩
  | comptime _ ih => obtain ⟨type, represented⟩ := ih; exact ⟨_, .comptime represented⟩

theorem default_represents_at {catalog : SourceCoreDataCatalog.Catalog} {signatures : ProgramSignatures}
    {functions : GenericHeap.PayloadModel catalog} {mapping : LocationMap} {world : StoreTyping}
    (layouts : CatalogLayouts catalog) {sourceType : TypeSystem.Ty} {source : Dynamic.Value}
    {value : Value} {expression : Expr} {type : Ty}
    (projected : catalog.project sourceType = .ok type)
    (tree : DataDefaults.Tree catalog sourceType source value expression) :
    ValueRep catalog signatures functions mapping world sourceType source value type := by
  obtain ⟨actual, represented⟩ := default_represents (signatures := signatures) (functions := functions) (mapping := mapping) (world := world) layouts tree
  have same := Except.ok.inj (represented.projection.symm.trans projected)
  exact same ▸ represented

/-- Existing finite constructor proofs embed without losing metadata. This
also keeps all earlier finite-heap clients compatible with the full model. -/
theorem finite_represents {catalog : SourceCoreDataCatalog.Catalog} {signatures : ProgramSignatures}
    {functions : GenericHeap.PayloadModel catalog} {mapping : LocationMap} {world : StoreTyping}
    {sourceType : TypeSystem.Ty} {source : Dynamic.Value} {value : Value}
    (represented : DataPatternTypedValues.TypedValueRep catalog signatures sourceType source value) :
    ∃ type, ValueRep catalog signatures functions mapping world sourceType source value type := by
  induction represented using DataPatternTypedValues.TypedValueRep.rec
    (motive_2 := fun types sources values _ => ∃ coreTypes,
      ValuesRep catalog signatures functions mapping world types sources values coreTypes) with
  | unit => exact ⟨_, .unit⟩
  | bool value => exact ⟨_, .bool value⟩
  | word value => exact ⟨_, .word value⟩
  | integer value => exact ⟨_, .integer value⟩
  | product _ _ first second =>
    obtain ⟨a, first⟩ := first
    obtain ⟨b, second⟩ := second
    exact ⟨_, .product first second⟩
  | @constructed sourceType metadata tag declaration arguments sources values nominal result authenticated original ih =>
    obtain ⟨types, payloads⟩ := ih
    obtain ⟨registered, projected, payload⟩ := DataValueTyping.resolveConstructor_payload authenticated
    have same := Except.ok.inj (payloads.projection.symm.trans projected)
    subst registered
    obtain ⟨coreType, projection, typed⟩ := DataValueTyping.TypedValueRep.project_typed
      (.constructed nominal result authenticated original)
    have typeEq : coreType = .namedData tag.owner := by cases typed []; rfl
    subst coreType
    exact ⟨_, .constructed nominal result authenticated projection payload payloads⟩
  | nil => exact ⟨[], .nil⟩
  | cons _ _ head tail =>
    obtain ⟨type, head⟩ := head
    obtain ⟨types, tail⟩ := tail
    exact ⟨_, .cons head tail⟩

end Solcore.SourceSemantics.CoreLowering.DataPayload
