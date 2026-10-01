import Solcore.SourceSemantics.CoreLowering.CompatiblePathUpdates

/-! Fault tokens are determined by the first unavailable raw default and its
authenticated registry ID. This source-level receipt is independent of native
child representations and lets recursive fault trees use one exact token. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleMixedRoute
open Core Frontend SourceInference SourceCoreCompatibleDataPlaces CompatiblePayload
open CompatibleMapping CompatibleMapping.MixedPaths

inductive FaultToken (checked : Checked) (registry : SourceCoreRawMetadata.Registry) :
    Dynamic.Value → List PreparedStep → List Dynamic.EvaluatedProjection → Dynamic.SemanticFault → Word → Nat → Prop where
  | missing {rawKey rawValue lookup entries index steps projections header}
      (metadata : MetadataRep registry (.mapping rawKey rawValue) header)
      (typed : Dynamic.ValueRuntimeType lookup rawKey)
      (absent : Dynamic.MappingAbsent lookup entries) (unavailable : ¬ Dynamic.Defaultable rawValue) :
      FaultToken checked registry (.mapping rawKey rawValue entries) (.index index :: steps) (.index lookup :: projections)
        (.missingMappingDefault rawValue) (index.missing.add header) (checked.catalog.entries.length + 1)
  | member {metadata values name position child dataType branches fieldType steps projections reason token count}
      (atField : Dynamic.ValueAt values position child)
      (tail : FaultToken checked registry child steps projections reason token count) :
      FaultToken checked registry (.constructed metadata values) (.member dataType position branches fieldType :: steps)
        (.member name position :: projections) reason token count
  | found {rawKey rawValue lookup entries index steps projections child reason token count}
      (typed : Dynamic.ValueRuntimeType lookup rawKey)
      (found : Dynamic.MappingLookup lookup entries child)
      (tail : FaultToken checked registry child steps projections reason token count) :
      FaultToken checked registry (.mapping rawKey rawValue entries) (.index index :: steps) (.index lookup :: projections)
        reason token (checked.catalog.entries.length + 1 + count)
  | default {rawKey rawValue lookup entries index steps projections child reason token count}
      (typed : Dynamic.ValueRuntimeType lookup rawKey)
      (absent : Dynamic.MappingAbsent lookup entries) (defaulted : Dynamic.DefaultValue rawValue child)
      (tail : FaultToken checked registry child steps projections reason token count) :
      FaultToken checked registry (.mapping rawKey rawValue entries) (.index index :: steps) (.index lookup :: projections)
        reason token (checked.catalog.entries.length + 1 + count)

 theorem FaultToken.functional {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
    {source : Dynamic.Value} {steps : List PreparedStep} {projections : List Dynamic.EvaluatedProjection}
    {reason : Dynamic.SemanticFault} {left right : Word} {firstCount secondCount : Nat}
    (first : FaultToken checked registry source steps projections reason left firstCount)
    (second : FaultToken checked registry source steps projections reason right secondCount) :
    left = right ∧ firstCount = secondCount := by
  induction first generalizing right secondCount with
  | missing metadata typed absent unavailable => cases second with
    | missing other _ _ _ => exact ⟨congrArg _ ((metadata.ids_equal_iff other).mpr rfl), rfl⟩
    | found _ found _ => exact (absent.excludes_lookup found).elim
    | default _ _ defaulted _ => exact (unavailable defaulted.defaultable).elim
  | member atField tail ih => cases second with
    | member other second =>
      have same := valueAt_unique atField other
      cases same
      exact ih second
  | found typed found tail ih => cases second with
    | missing _ _ absent _ => exact (absent.excludes_lookup found).elim
    | found _ other second =>
      have same := found.functional other
      cases same
      obtain ⟨token, count⟩ := ih second
      exact ⟨token, congrArg (fun n => _ + n) count⟩
    | default _ absent _ _ => exact (absent.excludes_lookup found).elim
  | default typed absent defaulted tail ih => cases second with
    | missing _ _ _ unavailable => exact (unavailable defaulted.defaultable).elim
    | found _ found _ => exact (absent.excludes_lookup found).elim
    | default _ _ other second =>
      have same := defaulted.functional other
      cases same
      obtain ⟨token, count⟩ := ih second
      exact ⟨token, congrArg (fun n => _ + n) count⟩

 theorem EntriesRep.lookup_payload {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
    {functions : FunctionModel checked.catalog} {mapping : GeneralHeap.LocationMap} {world : StoreTyping}
    {rawKey rawValue : TypeSystem.Ty} {lookup selected : Dynamic.Value}
    {sources : List (Dynamic.Value × Dynamic.Value)} {entries : OrderedMapping.Entries} {keyType valueType : Ty}
    (related : CompatiblePayload.EntriesRep checked registry functions mapping world rawKey rawValue sources entries keyType valueType)
    (found : Dynamic.MappingLookup lookup sources selected) :
    ∃ value, ValueRep checked registry functions mapping world rawValue selected value valueType := by
  induction found generalizing entries with
  | head _ => cases related with | entry key value rest => exact ⟨_, value⟩
  | tail _ found ih => cases related with | entry key value rest => exact ih rest

 theorem Selected.represented {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
    {functions : FunctionModel checked.catalog} {mapping : GeneralHeap.LocationMap} {world : StoreTyping}
    {rawKey rawValue : TypeSystem.Ty} {lookup selected : Dynamic.Value}
    {sources : List (Dynamic.Value × Dynamic.Value)} {header : Word} {layout : OrderedMapping.Layout}
    {entries : OrderedMapping.Entries} {fallback : Option Value}
    (fields : Fields checked registry functions mapping world rawKey rawValue sources header layout entries fallback)
    (selectedAt : Selected lookup sources rawValue selected) :
    ∃ value, ValueRep checked registry functions mapping world rawValue selected value layout.valueType := by
  cases selectedAt with
  | found found => exact EntriesRep.lookup_payload fields.stored found
  | default absent defaulted => cases fields.default with
    | absent unavailable => exact (unavailable defaulted.defaultable).elim
    | present other related =>
      have same := defaulted.functional other
      exact ⟨_, same.symm ▸ related⟩

end Solcore.SourceSemantics.CoreLowering.CompatibleMixedRoute
