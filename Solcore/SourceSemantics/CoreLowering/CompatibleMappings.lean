import Solcore.SourceSemantics.CoreLowering.CompatibleDefaults

/-! Ordered-entry and transported-default laws for the compatible payload
relation. Entries remain an ordered list: there is no deduplication, key
comparison, or normalization in this representation. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatiblePayload
open Core Frontend GeneralHeap
variable {checked : SourceCoreCompatibleCatalog.Checked} {registry : SourceCoreRawMetadata.Registry}
  {functions : FunctionModel checked.catalog} {mapping : LocationMap} {world : StoreTyping}

theorem DefaultRep.projection {sourceType : TypeSystem.Ty} {fallback : Option Value} {type : Ty}
    (related : DefaultRep checked registry functions mapping world sourceType fallback type) :
    checked.catalog.project sourceType = .ok type := by
  cases related with
  | absent _ projected => exact projected
  | present _ related => exact related.projection

theorem DefaultRep.runtime_hasType {sourceType : TypeSystem.Ty} {fallback : Option Value} {type : Ty}
    (related : DefaultRep checked registry functions mapping world sourceType fallback type) :
    RuntimeValueHasType world (OrderedMapping.optionValue type fallback) (.sum .unit type) checked.catalog.definitions := by
  cases related with
  | absent => exact .inLeft .unit
  | present _ related => exact .inRight related.runtime_hasType

theorem DefaultRep.extend {futureRegistry : SourceCoreRawMetadata.Registry} {futureMapping : LocationMap} {futureWorld : StoreTyping}
    {sourceType : TypeSystem.Ty} {fallback : Option Value} {type : Ty}
    (related : DefaultRep checked registry functions mapping world sourceType fallback type)
    (metadata : SourceCoreRawMetadata.Extends registry futureRegistry) (maps : LocationMap.Extends mapping futureMapping)
    (worlds : WorldExtends world futureWorld) :
    DefaultRep checked futureRegistry functions futureMapping futureWorld sourceType fallback type := by
  cases related with
  | absent missing projected wf => exact .absent missing projected wf
  | present meaning related => exact .present meaning (related.extend metadata maps worlds)

theorem EntriesRep.length {keyType valueType : TypeSystem.Ty} {sources : List (Dynamic.Value × Dynamic.Value)}
    {entries : OrderedMapping.Entries} {key value : Ty}
    (related : EntriesRep checked registry functions mapping world keyType valueType sources entries key value) :
    sources.length = entries.length := by
  induction sources generalizing entries with
  | nil => cases related; rfl
  | cons source sources ih => cases related with
    | entry _ _ tail => exact congrArg Nat.succ (ih tail)

/-- Every source entry has its corresponding native entry at the same index.
In particular, repeated source keys keep all their positions. -/
theorem EntriesRep.get {keyType valueType : TypeSystem.Ty} {sources : List (Dynamic.Value × Dynamic.Value)}
    {entries : OrderedMapping.Entries} {key value : Ty}
    (related : EntriesRep checked registry functions mapping world keyType valueType sources entries key value)
    {index : Nat} {sourceKey sourceValue : Dynamic.Value} (found : sources[index]? = some (sourceKey, sourceValue)) :
    ∃ a b, entries[index]? = some (a, b) ∧
      ValueRep checked registry functions mapping world keyType sourceKey a key ∧
      ValueRep checked registry functions mapping world valueType sourceValue b value := by
  induction index generalizing sources entries with
  | zero => cases related with
    | empty => simp at found
    | entry keyRep valueRep tail =>
      simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at found
      rcases found with ⟨rfl, rfl⟩
      exact ⟨_, _, rfl, keyRep, valueRep⟩
  | succ index ih => cases related with
    | empty => simp at found
    | entry _ _ tail => exact ih tail found

theorem EntriesRep.runtime_hasType {keyType valueType : TypeSystem.Ty} {sources : List (Dynamic.Value × Dynamic.Value)}
    {entries : OrderedMapping.Entries} {layout : OrderedMapping.Layout}
    (related : EntriesRep checked registry functions mapping world keyType valueType sources entries layout.keyType layout.valueType)
    (registered : layout.Registered checked.catalog.definitions) :
    RuntimeValueHasType world (OrderedMapping.encode layout entries) layout.type checked.catalog.definitions := by
  apply OrderedMapping.encode_hasType registered
  induction sources generalizing entries with
  | nil => cases related; simp
  | cons source sources ih =>
    cases related with
    | entry keyRep valueRep tail =>
      intro a b member
      rcases List.mem_cons.mp member with head | rest
      · cases head; exact ⟨keyRep.runtime_hasType, valueRep.runtime_hasType⟩
      · exact ih tail a b rest

theorem EntriesRep.extend {futureRegistry : SourceCoreRawMetadata.Registry} {futureMapping : LocationMap} {futureWorld : StoreTyping}
    {keyType valueType : TypeSystem.Ty} {sources : List (Dynamic.Value × Dynamic.Value)} {entries : OrderedMapping.Entries} {key value : Ty}
    (related : EntriesRep checked registry functions mapping world keyType valueType sources entries key value)
    (metadata : SourceCoreRawMetadata.Extends registry futureRegistry) (maps : LocationMap.Extends mapping futureMapping)
    (worlds : WorldExtends world futureWorld) :
    EntriesRep checked futureRegistry functions futureMapping futureWorld keyType valueType sources entries key value := by
  induction sources generalizing entries with
  | nil => cases related; exact .empty _ _ _ _
  | cons source sources ih => cases related with
    | entry first second tail => exact .entry (first.extend metadata maps worlds) (second.extend metadata maps worlds) (ih tail)

/-- Extract the authenticated raw header and exact ordered/default carriers
from any mapping payload, even behind a runtime-compatible type view. -/
theorem ValueRep.mapping_shape {sourceType : TypeSystem.Ty} {source : Dynamic.Value} {value : Value} {type : Ty}
    (related : ValueRep checked registry functions mapping world sourceType source value type) :
    ∀ {keyType valueType sources}, source = .mapping keyType valueType sources →
      ∃ id layout entries fallback,
        value = SourceCoreMappingWithDefault.value id fallback layout entries ∧
        type = SourceCoreMappingWithDefault.type layout ∧
        MetadataRep registry (.mapping keyType valueType) id ∧
        layout.Registered checked.catalog.definitions ∧
        EntriesRep checked registry functions mapping world keyType valueType sources entries layout.keyType layout.valueType ∧
        DefaultRep checked registry functions mapping world valueType fallback layout.valueType := by
  induction related using ValueRep.rec
    (motive_2 := fun _ _ _ _ _ => True) (motive_3 := fun _ _ _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ => True) with
  | unit | bool | word | integer | product | proxy | constructed => intro _ _ _ impossible; cases impossible
  | function related =>
    intro _ _ _ impossible
    have shape := functions.source_function related
    cases shape <;> cases impossible
  | mappingValue header _ _ _ registered stored fallback _ _ =>
    intro _ _ _ same
    cases same
    exact ⟨_, _, _, _, rfl, rfl, header, registered, stored, fallback⟩
  | compatible _ _ ih => exact ih
  | nil | cons | empty | entry | absent | present => trivial

/-- Equal native mapping header words mean equal original key/value metadata,
including all nested staging wrappers. -/
theorem mapping_headers_equal_iff {a b : Word} {leftKey leftValue rightKey rightValue : TypeSystem.Ty}
    (left : MetadataRep registry (.mapping leftKey leftValue) a)
    (right : MetadataRep registry (.mapping rightKey rightValue) b) :
    a = b ↔ leftKey = rightKey ∧ leftValue = rightValue := by
  simpa only [SourceCoreRawMetadata.Metadata.mapping.injEq] using left.ids_equal_iff right

end Solcore.SourceSemantics.CoreLowering.CompatiblePayload
