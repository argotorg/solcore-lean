import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicNestedInputs

/-! Induction statements for the original public codec. Each conclusion uses
one fixed receiving registry. Child receipts retain their own actual metadata
and extend forward into that registry. These statements are discharged by the
structural fold and real function issuance below. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicNestedEncodingContext
open Core Frontend SourceInference GeneralHeap CompatiblePayload DataPatternValues
open SourceCoreIndexedSession

variable {artifact : Artifact} (session : Session artifact)
  {checked : SourceCoreCompatibleCatalog.Checked}
  {ambient : AmbientDefinitions checked.catalog.definitions}
  (functions : FunctionModel checked.catalog ambient)
  (receiving : SourceCoreRawMetadata.Registry) (mapping : LocationMap) (world : StoreTyping)

def RawMeaning (sourceType : TypeSystem.Ty) (value : SourceCorePublicValues.Value)
    (source : Dynamic.Value) : Prop :=
  ∀ {fuel : Nat} {registry : SourceCoreRawMetadata.Registry} {expected : TypeSystem.Ty}
    {encoded : SourceCoreCompatibleValues.Extended registry Core.Value} {type : Ty},
    registry.signatures = checked.signatures →
    SourceCoreRawMetadata.runtimeType expected = SourceCoreRawMetadata.runtimeType sourceType →
    session.RawEncodedAt fuel registry expected value encoded →
    checked.catalog.project expected = .ok type →
    RuntimeValueHasType world encoded.value type ambient.definitions →
    SourceCoreRawMetadata.Extends encoded.registry receiving →
    ValueRep checked receiving functions mapping world
      sourceType source encoded.value type

def PayloadMeaning (types : List TypeSystem.Ty) (values : List SourceCorePublicValues.Value)
    (sources : List Dynamic.Value) : Prop :=
  ∀ {fuel : Nat} {registry : SourceCoreRawMetadata.Registry}
    {encoded : SourceCoreCompatibleValues.Extended registry Core.Value} {coreTypes : List Ty},
    registry.signatures = checked.signatures →
    session.PayloadsEncodedAt fuel registry types values encoded →
    types.mapM checked.catalog.project = .ok coreTypes →
    RuntimeValueHasType world encoded.value (SourceCoreCompatibleCatalog.packTypes coreTypes) ambient.definitions →
    SourceCoreRawMetadata.Extends encoded.registry receiving →
    ∃ native, ValuesRep checked receiving functions mapping world
      types sources native coreTypes ∧ encoded.value = packValues native

def EntriesMeaning (key value : TypeSystem.Ty)
    (entries : List (SourceCorePublicValues.Value × SourceCorePublicValues.Value))
    (sources : List (Dynamic.Value × Dynamic.Value)) : Prop :=
  ∀ {fuel : Nat} {registry : SourceCoreRawMetadata.Registry} {layout : OrderedMapping.Layout}
    {encoded : SourceCoreCompatibleValues.Extended registry Core.Value},
    registry.signatures = checked.signatures →
    session.EntriesEncodedAt fuel registry key value layout entries encoded →
    checked.catalog.project key = .ok layout.keyType →
    checked.catalog.project value = .ok layout.valueType →
    layout.Registered checked.catalog.definitions →
    RuntimeValueHasType world encoded.value layout.type ambient.definitions →
    SourceCoreRawMetadata.Extends encoded.registry receiving →
    ∃ native, EntriesRep checked receiving functions mapping world
      key value sources native layout.keyType layout.valueType ∧ encoded.value = OrderedMapping.encode layout native

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicNestedEncodingContext
