import Solcore.SourceSemantics.CoreLowering.CompatibleMappingComparison
import Solcore.SourceSemantics.CoreLowering.CompatibleMappings

/-! Ordered source entries keep full compatible payload receipts throughout
lookup and replacement. Equality observations never replace those receipts. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleMapping
open Core Frontend CompatiblePayload CompatibleEquality

abbrev Payload {checked : SourceCoreCompatibleCatalog.Checked} (registry : Registry)
    {ambient : AmbientDefinitions checked.catalog.definitions}
    (functions : FunctionModel checked.catalog ambient) (mapping : GeneralHeap.LocationMap) (world : StoreTyping)
    (sourceType : TypeSystem.Ty) (type : Ty) : OrderedMapping.Relation :=
  fun source value => ValueRep checked registry functions mapping world sourceType source value type

variable {checked : SourceCoreCompatibleCatalog.Checked} {registry : Registry}
  {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {mapping : GeneralHeap.LocationMap} {world : StoreTyping}
  {sourceKey sourceValue : TypeSystem.Ty} {keyType valueType : Ty}

 theorem entries_related {sources : List (Dynamic.Value × Dynamic.Value)} {entries : Core.OrderedMapping.Entries}
    (related : EntriesRep checked registry functions mapping world sourceKey sourceValue sources entries keyType valueType) :
    OrderedMapping.EntriesRel (Payload registry functions mapping world sourceKey keyType)
      (Payload registry functions mapping world sourceValue valueType) sources entries := by
  induction sources generalizing entries with
  | nil => cases related; exact .nil
  | cons head tail ih => cases related with
    | entry key value tail => exact .cons key value (ih tail)

 theorem entries_of_related {sources : List (Dynamic.Value × Dynamic.Value)} {entries : Core.OrderedMapping.Entries}
    (related : OrderedMapping.EntriesRel (Payload registry functions mapping world sourceKey keyType)
      (Payload registry functions mapping world sourceValue valueType) sources entries) :
    EntriesRep checked registry functions mapping world sourceKey sourceValue sources entries keyType valueType := by
  induction related with
  | nil => exact .empty _ _ _ _
  | cons key value tail ih => exact .entry key value ih

 theorem entries_observed (prepared : SourceCoreCompatibleDataEquality.Prepared checked)
    {identities : Dynamic.Value → Word → Prop}
    (functionLeaves : FunctionObservations checked.catalog functions identities)
    (keyProjected : keyType = prepared.type)
    {sources : List (Dynamic.Value × Dynamic.Value)} {entries : Core.OrderedMapping.Entries}
    (related : EntriesRep checked registry functions mapping world sourceKey sourceValue sources entries keyType valueType) :
    OrderedMapping.EntriesRel (CompatibleMappingComparison.KeyRep prepared registry identities)
      (Payload registry functions mapping world sourceValue valueType) sources entries := by
  subst keyType
  induction sources generalizing entries with
  | nil => cases related; exact .nil
  | cons head tail ih => cases related with
    | entry key value tail => exact .cons (CompatibleEquality.ValueRep.observation functionLeaves key) value (ih tail)

 theorem predicate_correct (prepared : SourceCoreCompatibleDataEquality.Prepared checked)
    {identities : Dynamic.Value → Word → Prop}
    (functionLeaves : FunctionObservations checked.catalog functions identities)
    (keyProjected : keyType = prepared.type) {equal : Core.OrderedMapping.Predicate}
    (correct : OrderedMapping.KeyEqualityCorrect (CompatibleMappingComparison.KeyRep prepared registry identities) equal) :
    OrderedMapping.KeyEqualityCorrect (Payload registry functions mapping world sourceKey keyType) equal := by
  subst keyType
  exact ⟨fun a b => correct.equivalent
    (CompatibleEquality.ValueRep.observation functionLeaves a) (CompatibleEquality.ValueRep.observation functionLeaves b)⟩

/-- Classification of real mathematical ordered lookup, independent of any
source evaluator or native helper. -/
inductive Lookup (key : Dynamic.Value) (sources : List (Dynamic.Value × Dynamic.Value)) : Option Dynamic.Value → Prop where
  | found {value} (found : Dynamic.MappingLookup key sources value) : Lookup key sources (some value)
  | absent (absent : Dynamic.MappingAbsent key sources) : Lookup key sources none

 theorem lookup_total (key : Dynamic.Value) (sources : List (Dynamic.Value × Dynamic.Value)) : ∃ found, Lookup key sources found := by
  classical
  induction sources with
  | nil => exact ⟨none, .absent .nil⟩
  | cons entry rest ih =>
    by_cases same : Dynamic.ValueEquivalent key entry.1
    · exact ⟨some entry.2, .found (.head same)⟩
    · obtain ⟨found, ih⟩ := ih
      cases ih with
      | found found => exact ⟨_, .found (.tail same found)⟩
      | absent absent => exact ⟨_, .absent (.cons same absent)⟩

 theorem insert_total (key value : Dynamic.Value) (sources : List (Dynamic.Value × Dynamic.Value)) :
    ∃ updated, Dynamic.MappingInsert key value sources updated := by
  classical
  induction sources with
  | nil => exact ⟨_, .append .nil⟩
  | cons entry rest ih =>
    by_cases same : Dynamic.ValueEquivalent key entry.1
    · exact ⟨_, .update (.head same)⟩
    · obtain ⟨updated, ih⟩ := ih
      cases ih with
      | update replacement => exact ⟨_, .update (.tail same replacement)⟩
      | append absent => exact ⟨_, .append (.cons same absent)⟩

 theorem lookup_preserves {equal : Core.OrderedMapping.Predicate}
    (correct : OrderedMapping.KeyEqualityCorrect (Payload registry functions mapping world sourceKey keyType) equal)
    {sourceLookup sourceResult : Dynamic.Value} {key : Value}
    {sources : List (Dynamic.Value × Dynamic.Value)} {entries : Core.OrderedMapping.Entries}
    (keyRep : Payload registry functions mapping world sourceKey keyType sourceLookup key)
    (related : EntriesRep checked registry functions mapping world sourceKey sourceValue sources entries keyType valueType)
    (found : Dynamic.MappingLookup sourceLookup sources sourceResult) :
    ∃ result, Core.OrderedMapping.lookupEntries equal key entries = some result ∧
      Payload registry functions mapping world sourceValue valueType sourceResult result :=
  OrderedMapping.lookup_related correct keyRep (entries_related related) found

 theorem insert_preserves {equal : Core.OrderedMapping.Predicate}
    (correct : OrderedMapping.KeyEqualityCorrect (Payload registry functions mapping world sourceKey keyType) equal)
    {sourceLookup sourceReplacement : Dynamic.Value} {key replacement : Value}
    {sources updated : List (Dynamic.Value × Dynamic.Value)} {entries : Core.OrderedMapping.Entries}
    (keyRep : Payload registry functions mapping world sourceKey keyType sourceLookup key)
    (replacementRep : Payload registry functions mapping world sourceValue valueType sourceReplacement replacement)
    (related : EntriesRep checked registry functions mapping world sourceKey sourceValue sources entries keyType valueType)
    (inserted : Dynamic.MappingInsert sourceLookup sourceReplacement sources updated) :
    EntriesRep checked registry functions mapping world sourceKey sourceValue updated
      (Core.OrderedMapping.insertEntries equal key replacement entries) keyType valueType :=
  entries_of_related (OrderedMapping.insert_related correct keyRep replacementRep (entries_related related) inserted)

end Solcore.SourceSemantics.CoreLowering.CompatibleMapping
