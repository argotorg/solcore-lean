import Solcore.SourceSemantics.CoreLowering.DataPayloadEquality
import Solcore.SourceSemantics.CoreLowering.DataPlaceMappingIndex

/-! Actual mapping insertion retains the complete representations of both keys
and values. The comparator only needs equality observations, but that weaker
observation must not replace the stored key's code/data authentication. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataPayload
open Core Frontend Frontend.SourceInference GeneralHeap DataPatternValues DataEquality

variable {catalog : SourceCoreDataCatalog.Catalog} {signatures : ProgramSignatures}
  {functions : GenericHeap.PayloadModel catalog} {mapping : LocationMap} {world : StoreTyping}

theorem EntriesRep.of_ordered {key value : TypeSystem.Ty} {keyType valueType : Ty}
    {sources : List (Dynamic.Value × Dynamic.Value)} {entries : Core.OrderedMapping.Entries}
    (represented : OrderedMapping.EntriesRel
      (fun source core => ValueRep catalog signatures functions mapping world key source core keyType)
      (fun source core => ValueRep catalog signatures functions mapping world value source core valueType) sources entries) :
    EntriesRep catalog signatures functions mapping world key value keyType valueType sources entries := by
  induction represented with
  | nil => exact .empty _ _ _ _
  | cons key value _ ih => exact .prepend key value ih

/-- The exact generated insertion uses full keys for representation, and only
for comparison projects those keys to their source equality observations. The
output relation never authenticates a closure from equality observations. -/
theorem insert_preserves {checked : SourceCoreDataCatalog.Checked} {signatures : ProgramSignatures}
    {functions : GenericHeap.PayloadModel checked.catalog} {mapping : LocationMap} {world : StoreTyping}
    {identities : Dynamic.Value → Word → Prop}
    (observations : FunctionObservations checked.catalog signatures functions identities)
    (faithful : IdentityFaithful identities) (prepared : SourceCoreDataEquality.Prepared checked)
    (layout : Core.OrderedMapping.Layout) (comparisonType : layout.keyType = prepared.type)
    {keyType valueType : TypeSystem.Ty}
    (identity : checked.catalog.identity? (.mapping keyType valueType) = some layout.dataType)
    (keyProjection : checked.catalog.project keyType = .ok layout.keyType)
    (valueProjection : checked.catalog.project valueType = .ok layout.valueType)
    (registered : layout.Registered checked.catalog.definitions)
    {sourceKey sourceValue : Dynamic.Value} {key value : Value}
    {sources updated : List (Dynamic.Value × Dynamic.Value)} {entries : Core.OrderedMapping.Entries}
    (keyRep : ValueRep checked.catalog signatures functions mapping world keyType sourceKey key layout.keyType)
    (valueRep : ValueRep checked.catalog signatures functions mapping world valueType sourceValue value layout.valueType)
    (related : EntriesRep checked.catalog signatures functions mapping world keyType valueType layout.keyType layout.valueType sources entries)
    (inserted : Dynamic.MappingInsert sourceKey sourceValue sources updated)
    (environment : Environment) (store : Store) (current keyExpression valueExpression : Expr)
    (currentSelected : Selects environment current (Core.OrderedMapping.encode layout entries))
    (keySelected : Selects environment keyExpression key) (valueSelected : Selects environment valueExpression value) :
    ∃ output,
      ValueRep checked.catalog signatures functions mapping world (.mapping keyType valueType)
        (.mapping keyType valueType updated) output layout.type ∧
      Evaluates environment store (Core.OrderedMapping.insert layout prepared.expression current keyExpression valueExpression)
        (.inRight .word output) (DataMappingComparison.insertStore prepared layout environment store entries key value) := by
  have keyObserved : DataMappingComparison.KeyRep prepared signatures identities sourceKey key := by
    unfold DataMappingComparison.KeyRep; rw [← comparisonType]; exact keyRep.observation observations
  have entriesObserved : OrderedMapping.EntriesRel (DataMappingComparison.KeyRep prepared signatures identities)
      (fun source core => ValueRep checked.catalog signatures functions mapping world valueType source core layout.valueType) sources entries := by
    unfold DataMappingComparison.KeyRep
    rw [← comparisonType]
    exact related.observed observations
  obtain ⟨equal, correct⟩ := DataMappingComparison.exists_predicate_correct prepared signatures faithful
  have fullCorrect : OrderedMapping.KeyEqualityCorrect
      (fun source core => ValueRep checked.catalog signatures functions mapping world keyType source core layout.keyType) equal := by
    constructor
    intro sourceKey sourceStored key stored first second
    apply correct.equivalent
    · unfold DataMappingComparison.KeyRep; rw [← comparisonType]; exact first.observation observations
    · unfold DataMappingComparison.KeyRep; rw [← comparisonType]; exact second.observation observations
  have resultRelated := OrderedMapping.insert_related fullCorrect keyRep valueRep related.ordered inserted
  exact ⟨_, .mapping identity keyProjection valueProjection registered (EntriesRep.of_ordered resultRelated),
    DataMappingComparison.insert_evaluates prepared layout comparisonType faithful equal correct keyObserved entriesObserved
      environment store current keyExpression valueExpression currentSelected keySelected valueSelected⟩

/-- Found lookup also retains the complete selected value. Comparison projects
stored keys to observations without modifying their stronger relation. -/
theorem lookup_found {checked : SourceCoreDataCatalog.Checked} {signatures : ProgramSignatures}
    {functions : GenericHeap.PayloadModel checked.catalog} {mapping : LocationMap} {world : StoreTyping}
    {identities : Dynamic.Value → Word → Prop}
    (observations : FunctionObservations checked.catalog signatures functions identities)
    (faithful : IdentityFaithful identities) (prepared : SourceCoreDataEquality.Prepared checked)
    (layout : Core.OrderedMapping.Layout) (comparisonType : layout.keyType = prepared.type)
    {keyType valueType : TypeSystem.Ty} {sourceKey sourceValue : Dynamic.Value} {key : Value}
    {sources : List (Dynamic.Value × Dynamic.Value)} {entries : Core.OrderedMapping.Entries}
    (keyRep : ValueRep checked.catalog signatures functions mapping world keyType sourceKey key layout.keyType)
    (related : EntriesRep checked.catalog signatures functions mapping world keyType valueType layout.keyType layout.valueType sources entries)
    (found : Dynamic.MappingLookup sourceKey sources sourceValue)
    (environment : Environment) (store : Store) (current keyExpression : Expr)
    (currentSelected : Selects environment current (Core.OrderedMapping.encode layout entries))
    (keySelected : Selects environment keyExpression key) :
    ∃ output, ValueRep checked.catalog signatures functions mapping world valueType sourceValue output layout.valueType ∧
      Evaluates environment store (Core.OrderedMapping.lookup layout prepared.expression current keyExpression)
        (.inRight .word (.inRight .unit output)) (DataMappingComparison.lookupStore prepared layout environment store entries key) := by
  apply DataMappingComparison.lookup_found (signatures := signatures) prepared layout comparisonType faithful (valueRel :=
    fun source core => ValueRep checked.catalog signatures functions mapping world valueType source core layout.valueType)
    ?_ ?_ found environment store current keyExpression currentSelected keySelected
  · unfold DataMappingComparison.KeyRep; rw [← comparisonType]; exact keyRep.observation observations
  · unfold DataMappingComparison.KeyRep
    rw [← comparisonType]
    exact related.observed observations

end Solcore.SourceSemantics.CoreLowering.DataPayload
