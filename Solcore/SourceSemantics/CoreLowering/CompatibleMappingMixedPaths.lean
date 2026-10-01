import Solcore.SourceSemantics.CoreLowering.CompatiblePayloadMembers
import Solcore.SourceSemantics.CoreLowering.CompatibleMappingPlaceRuns

/-! Structural certificates for the actual compatible mixed selector. Each
node retains complete payload authentication. Mapping tails consume the actual
lookup/default payload relation; no child runtime evaluation is assumed. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleMapping.MixedPaths
open Core Frontend SourceInference CompatiblePayload CompatibleEquality DataEquality DataPatternValues
open SourceCoreCompatibleDataPlaces

inductive Selected (key : Dynamic.Value) (entries : List (Dynamic.Value × Dynamic.Value))
    (type : TypeSystem.Ty) : Dynamic.Value → Prop where
  | found {value} : Dynamic.MappingLookup key entries value → Selected key entries type value
  | default {value} : Dynamic.MappingAbsent key entries → Dynamic.DefaultValue type value → Selected key entries type value

theorem Selected.payload {checked : SourceCoreCompatibleCatalog.Checked} {registry : Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {mapping : GeneralHeap.LocationMap} {world : StoreTyping}
    {key source : Dynamic.Value} {entries : List (Dynamic.Value × Dynamic.Value)} {type : TypeSystem.Ty}
    (selected : Selected key entries type source) {nativeType : Ty} {missing header : Word} {result : Value}
    (meaning : ReadResult checked registry functions mapping world type key entries nativeType missing header result) :
    ∃ value, result = .inRight .word value ∧ Payload registry functions mapping world type nativeType source value := by
  cases selected with
  | found found => cases meaning with
    | found other represented => exact ⟨_, rfl, found.functional other ▸ represented⟩
    | default absent _ _ => exact (absent.excludes_lookup found).elim
    | missing absent _ => exact (absent.excludes_lookup found).elim
  | default absent defaulted => cases meaning with
    | found found _ => exact (absent.excludes_lookup found).elim
    | default _ other represented => exact ⟨_, rfl, defaulted.functional other ▸ represented⟩
    | missing _ unavailable => exact (unavailable defaulted.defaultable).elim

inductive ReadTree (checked : SourceCoreCompatibleCatalog.Checked) (registry : Registry)
    {ambient : AmbientDefinitions checked.catalog.definitions}
    (functions : FunctionModel checked.catalog ambient) (mapping : GeneralHeap.LocationMap) (world : StoreTyping)
    (prepared : Prepared) (keys : List Value) (leafType : TypeSystem.Ty) (leafCore : Ty) :
    TypeSystem.Ty → Dynamic.Value → Value → List PreparedStep → List Dynamic.EvaluatedProjection → Dynamic.Value → Nat → Prop where
  | leaf {source value} (related : ValueRep checked registry functions mapping world leafType source value leafCore) :
      ReadTree checked registry functions mapping world prepared keys leafType leafCore leafType source value [] [] source 0
  | compatible {expected actual source value steps projections leaf count}
      (view : SourceCoreRawMetadata.runtimeType expected = SourceCoreRawMetadata.runtimeType actual)
      (tail : ReadTree checked registry functions mapping world prepared keys leafType leafCore actual source value steps projections leaf count) :
      ReadTree checked registry functions mapping world prepared keys leafType leafCore expected source value steps projections leaf count
  | member {expected metadata tag id sources values types dataType index branches branch fieldType childType name}
      {sourceChild valueChild steps projections leaf count}
      (fields : ConstructorFields checked registry functions mapping world expected metadata tag id sources values types)
      (owner : tag.owner = dataType) (branchAt : branches[tag.index]? = some branch)
      (constructor : branch.constructor = tag) (branchTypes : branch.payloadTypes = types)
      (field : metadata.payloadTypes[index]? = some childType) (fieldCore : types[index]? = some fieldType)
      (sourceAt : Dynamic.ValueAt sources index sourceChild) (coreAt : values[index]? = some valueChild)
      (tail : ReadTree checked registry functions mapping world prepared keys leafType leafCore childType sourceChild valueChild steps projections leaf count) :
      ReadTree checked registry functions mapping world prepared keys leafType leafCore expected
        (.constructed metadata sources) (.constructed tag (.pair (.word id) (packValues values)))
        (.member dataType index branches fieldType :: steps) (.member name index :: projections) leaf count
  | mapping {sourceKey sourceValue index sources header entries fallback lookup key child steps projections leaf count}
      (certificate : Index checked index)
      (fields : Fields checked registry functions mapping world sourceKey sourceValue sources header index.layout entries fallback)
      (keyRep : Payload registry functions mapping world sourceKey index.layout.keyType lookup key)
      (keyAt : keys[index.keyPosition]? = some key)
      (selected : Selected lookup sources sourceValue child)
      (tail : ∀ value, Payload registry functions mapping world sourceValue index.layout.valueType child value →
        ReadTree checked registry functions mapping world prepared keys leafType leafCore sourceValue child value steps projections leaf count) :
      ReadTree checked registry functions mapping world prepared keys leafType leafCore (.mapping sourceKey sourceValue)
        (.mapping sourceKey sourceValue sources) (Transport.carrier header fallback index.layout entries)
        (.index index :: steps) (.index lookup :: projections) leaf (checked.catalog.entries.length + 1 + count)

theorem ReadTree.preserves {checked : SourceCoreCompatibleCatalog.Checked} {registry : Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {mapping : GeneralHeap.LocationMap} {world : StoreTyping}
    {prepared : Prepared} {keys : List Value} {leafType sourceType : TypeSystem.Ty} {leafCore : Ty}
    {source leaf : Dynamic.Value} {value : Value} {steps : List PreparedStep} {projections : List Dynamic.EvaluatedProjection} {count : Nat}
    (tree : ReadTree checked registry functions mapping world prepared keys leafType leafCore sourceType source value steps projections leaf count)
    {identities : Dynamic.Value → Word → Prop} (faithful : IdentityFaithful identities)
    (functionLeaves : FunctionObservations checked.catalog functions identities) (keyLength : prepared.keyTypes.length = keys.length)
    (environment : Environment) (store : Store) (current keyExpression : Expr)
    (selected : Selects environment current value) (keysSelected : Selects environment keyExpression (packValues keys)) :
    ∃ native finalStore administrative,
      Dynamic.ProjectionsRead (some source) projections (some leaf) ∧
      ValueRep checked registry functions mapping world leafType leaf native leafCore ∧
      Evaluates environment store (select prepared steps current keyExpression) (.inRight .word (.inRight .unit native)) finalStore ∧
      finalStore = store ++ administrative ∧ administrative.length = count := by
  induction tree generalizing environment store current keyExpression with
  | leaf related => exact ⟨_, store, [], .nil, related, .inRight (.inRight (selected.evaluates store)), by simp, rfl⟩
  | compatible _ _ ih => exact ih environment store current keyExpression selected keysSelected
  | @member expected metadata tag id sources values types dataType index branches branch fieldType childType name sourceChild valueChild steps projections leaf count fields owner branchAt constructor branchTypes field fieldCore sourceAt coreAt tail ih =>
    have arity : branch.payloadTypes.length = values.length := branchTypes ▸ (fields.payloads.length.2.2.symm.trans fields.payloads.length.2.1)
    let payload := Value.pair (.word id) (packValues values)
    obtain ⟨native, finalStore, administrative, read, related, evaluated, appended, counted⟩ :=
      ih (payload :: environment) store _ (shift 1 keyExpression)
        (projectPacked_selects (.second (.var (index := 0) rfl)) arity index coreAt)
        (by simpa [shift] using keysSelected.weaken payload)
    exact ⟨native, finalStore, administrative, .member sourceAt read, related,
      .matchData (selected.evaluates store) owner (by simp only [List.getElem?_map, branchAt, Option.map_some]) evaluated,
      appended, counted⟩
  | @mapping sourceKey sourceValue index sources header entries fallback lookup key child steps projections leaf count certificate fields keyRep keyAt read tail ih =>
    have keySelected := projectPacked_selects keysSelected keyLength index.keyPosition keyAt
    obtain ⟨result, meaning, evaluated⟩ := selectedIndex_meaning certificate prepared faithful functionLeaves fields keyRep
      environment store current keyExpression selected keySelected
    obtain ⟨native, rfl, related⟩ := read.payload meaning
    obtain ⟨leafNative, finalStore, after, tailRead, represented, tailEvaluated, appended, counted⟩ :=
      ih native related (native :: environment) _ (.var 0) (shift 1 keyExpression) (.var rfl)
        (by simpa [shift] using keysSelected.weaken native)
    obtain ⟨before, beforeAppended, firstCount⟩ := Transport.lookupStore_extension certificate.comparison index.layout environment store header fallback entries key
    refine ⟨leafNative, finalStore, before ++ after, ?_, represented, LanguageResult.bind_success _ evaluated tailEvaluated, ?_, ?_⟩
    · cases read with
      | found found => exact .indexFound found tailRead
      | default absent defaulted => exact .indexDefault absent defaulted tailRead
    · rw [appended, beforeAppended, List.append_assoc]
    · simp only [List.length_append, firstCount, counted]

end Solcore.SourceSemantics.CoreLowering.CompatibleMapping.MixedPaths
