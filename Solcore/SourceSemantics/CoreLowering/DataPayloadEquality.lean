import Solcore.SourceSemantics.CoreLowering.DataPayload

/-! Equality observations extracted from the complete data payload relation.
Function identity authentication remains a separate law of the function model;
there is no generic equality of function code or captured heaps. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataPayload
open Core Frontend Frontend.SourceInference GeneralHeap DataPatternValues DataEqualityValues

/-- Additional observation law needed only by source equality. Future function
carriers may establish this law through their own authenticated adapter. -/
def FunctionObservations (catalog : SourceCoreDataCatalog.Catalog) (signatures : ProgramSignatures)
    (functions : GenericHeap.PayloadModel catalog) (identities : Dynamic.Value → Word → Prop) : Prop :=
  ∀ {mapping world parameter result source value type},
    functions.Represents mapping world (.function parameter result) source value type →
    Observation catalog signatures identities type source value

theorem ValueRep.observation {catalog : SourceCoreDataCatalog.Catalog} {signatures : ProgramSignatures}
    {functions : GenericHeap.PayloadModel catalog} {identities : Dynamic.Value → Word → Prop}
    (functionObservations : FunctionObservations catalog signatures functions identities)
    {mapping : LocationMap} {world : StoreTyping} {sourceType : TypeSystem.Ty} {source : Dynamic.Value} {value : Value} {type : Ty}
    (represented : ValueRep catalog signatures functions mapping world sourceType source value type) :
    Observation catalog signatures identities type source value := by
  induction represented using ValueRep.rec
    (motive_2 := fun _ sources values types _ => ∃ packed, Dynamic.ValuesPack sources packed ∧
      Observation catalog signatures identities (SourceCoreDataMatches.bundleType types) packed (packValues values))
    (motive_3 := fun _ _ _ _ _ _ _ => True) with
  | unit => exact .unit
  | bool value => exact .bool value
  | word value => exact .word value
  | integer value => exact .integer value
  | product _ _ first second => exact .product first second
  | function represented => exact functionObservations represented
  | proxy identity _ => exact .proxy_of_identity identity
  | mapping identity _ _ _ _ _ => exact .mapping_of_identity identity _ _
  | @constructed sourceType metadata tag declaration arguments sources values types nominal result authenticated projection registered payloads ih =>
    obtain ⟨packed, packing, observed⟩ := ih
    have identity := DataPatternAuthenticity.constructor_identity (SourceCoreDataValues.resolveConstructor_lookup authenticated)
    obtain ⟨entry, selected, sourceTypeEq⟩ := identity_entry identity
    have nominalResult : SourceCoreDataCatalog.nominalParts metadata.resultType = some (declaration, arguments) := by
      rw [result]; exact nominal
    rw [erase_nominal nominalResult] at sourceTypeEq
    exact .constructed selected sourceTypeEq nominalResult authenticated registered
      payloads.length.1.symm packing observed
  | comptime _ ih => exact ih
  | nil => exact ⟨.unit, .nil, .unit⟩
  | cons head tail first rest =>
    obtain ⟨packed, packing, observed⟩ := rest
    cases tail with
    | nil => exact ⟨_, .singleton _, first⟩
    | cons => exact ⟨_, .cons packing, .product first observed⟩
  | empty | prepend => trivial

/-- Every stored key receives its authentic source equality observation from
its full representation. Entry order and duplicate keys are preserved. -/
theorem EntriesRep.observed {catalog : SourceCoreDataCatalog.Catalog} {signatures : ProgramSignatures}
    {functions : GenericHeap.PayloadModel catalog} {identities : Dynamic.Value → Word → Prop}
    (functionObservations : FunctionObservations catalog signatures functions identities)
    {mapping : LocationMap} {world : StoreTyping} {key value : TypeSystem.Ty} {keyType valueType : Ty}
    {sources : List (Dynamic.Value × Dynamic.Value)} {entries : Core.OrderedMapping.Entries}
    (represented : EntriesRep catalog signatures functions mapping world key value keyType valueType sources entries) :
    OrderedMapping.EntriesRel (Observation catalog signatures identities keyType)
      (fun source core => ValueRep catalog signatures functions mapping world value source core valueType) sources entries := by
  induction sources generalizing entries with
  | nil => cases represented; exact .nil
  | cons source sources ih => cases represented with
    | prepend key value rest => exact .cons (key.observation functionObservations) value (ih rest)

end Solcore.SourceSemantics.CoreLowering.DataPayload
