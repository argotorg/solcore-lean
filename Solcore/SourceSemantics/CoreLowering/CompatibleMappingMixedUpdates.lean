import Solcore.SourceSemantics.CoreLowering.CompatibleMappingMixedPaths
import Solcore.SourceSemantics.CoreLowering.DataPlaceMembers

/-! Full-payload reconstruction for compatible mixed paths. The selected raw
constructor ID and mapping header/default are kept; each mapping lookup occurs
before its child update and insertion. Child execution is derived from Trees. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleMapping.MixedPaths
open Core Frontend SourceInference CompatiblePayload CompatibleEquality DataEquality DataPatternValues
open SourceCoreCompatibleDataPlaces

inductive UpdateTree (checked : SourceCoreCompatibleCatalog.Checked) (registry : Registry)
    {ambient : AmbientDefinitions checked.catalog.definitions}
    (functions : FunctionModel checked.catalog ambient) (mapping : GeneralHeap.LocationMap) (world : StoreTyping)
    (prepared : Prepared) (keys : List Value) (replacementSource : Dynamic.Value) (replacement : Value) :
    TypeSystem.Ty → Dynamic.Value → Value → Ty → List PreparedStep → List Dynamic.EvaluatedProjection → Dynamic.Value → Nat → Prop where
  | leaf {sourceType source value type}
      (related : ValueRep checked registry functions mapping world sourceType replacementSource replacement type) :
      UpdateTree checked registry functions mapping world prepared keys replacementSource replacement sourceType source value type [] [] replacementSource 0
  | compatible {expected actual source value type steps projections updated count}
      (view : SourceCoreRawMetadata.runtimeType expected = SourceCoreRawMetadata.runtimeType actual)
      (tail : UpdateTree checked registry functions mapping world prepared keys replacementSource replacement actual source value type steps projections updated count) :
      UpdateTree checked registry functions mapping world prepared keys replacementSource replacement expected source value type steps projections updated count
  | member {expected metadata tag id sources values types dataType index branches branch fieldType childType name}
      {sourceChild valueChild updatedChild steps projections count}
      (fields : ConstructorFields checked registry functions mapping world expected metadata tag id sources values types)
      (owner : tag.owner = dataType) (branchAt : branches[tag.index]? = some branch)
      (constructor : branch.constructor = tag) (branchTypes : branch.payloadTypes = types)
      (field : metadata.payloadTypes[index]? = some childType) (fieldCore : types[index]? = some fieldType)
      (sourceAt : Dynamic.ValueAt sources index sourceChild) (coreAt : values[index]? = some valueChild)
      (tail : UpdateTree checked registry functions mapping world prepared keys replacementSource replacement childType sourceChild valueChild fieldType steps projections updatedChild count) :
      UpdateTree checked registry functions mapping world prepared keys replacementSource replacement expected
        (.constructed metadata sources) (.constructed tag (.pair (.word id) (packValues values))) (.namedData tag.owner)
        (.member dataType index branches fieldType :: steps) (.member name index :: projections)
        (.constructed metadata (sources.set index updatedChild)) count
  | mapping {sourceKey sourceValue index sources header entries fallback lookup key child updatedChild updatedEntries steps projections count}
      (certificate : Index checked index)
      (fields : Fields checked registry functions mapping world sourceKey sourceValue sources header index.layout entries fallback)
      (keyRep : Payload registry functions mapping world sourceKey index.layout.keyType lookup key)
      (keyAt : keys[index.keyPosition]? = some key)
      (selected : Selected lookup sources sourceValue child)
      (tail : ∀ value, Payload registry functions mapping world sourceValue index.layout.valueType child value →
        UpdateTree checked registry functions mapping world prepared keys replacementSource replacement sourceValue child value index.layout.valueType steps projections updatedChild count)
      (inserted : Dynamic.MappingInsert lookup updatedChild sources updatedEntries) :
      UpdateTree checked registry functions mapping world prepared keys replacementSource replacement (.mapping sourceKey sourceValue)
        (.mapping sourceKey sourceValue sources) (Transport.carrier header fallback index.layout entries) (SourceCoreMappingWithDefault.type index.layout)
        (.index index :: steps) (.index lookup :: projections) (.mapping sourceKey sourceValue updatedEntries)
        (2 * (checked.catalog.entries.length + 1) + count)

private theorem replaceAt {values : List Dynamic.Value} {index : Nat} {previous : Dynamic.Value}
    (selected : Dynamic.ValueAt values index previous) (replacement : Dynamic.Value) :
    Dynamic.ValuesReplaceAt values index replacement (values.set index replacement) := by
  induction selected with
  | head => exact .head
  | tail _ ih => exact .tail ih

private theorem pack_eq (expressions : List Expr) : pack expressions = SourceCoreDataPlaces.pack expressions := by
  induction expressions with
  | nil => rfl
  | cons head tail ih => cases tail with
    | nil => rfl
    | cons next rest => simp only [pack, SourceCoreDataPlaces.pack, ih]

/-- Both frontends use this same structural bundle replacement expression.
The reused theorem has no strict catalog or source payload assumptions. -/
theorem replacePacked_evaluates {environment : Environment} {store : Store}
    {index : Nat} {types : List Ty} {values : List Value} {payload replacement : Expr} {value : Value}
    (length : types.length = values.length) (selected : Selects environment payload (packValues values))
    (newValue : Selects environment replacement value) :
    Evaluates environment store (replacePacked index types payload replacement) (packValues (values.set index value)) store := by
  simpa only [replacePacked, SourceCoreDataPlaces.replacePacked, pack_eq] using
    (DataPlaceMembers.replacePacked_evaluates (index := index) (store := store) length selected newValue)

theorem UpdateTree.preserves {checked : SourceCoreCompatibleCatalog.Checked} {registry : Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {mapping : GeneralHeap.LocationMap} {world : StoreTyping}
    {prepared : Prepared} {keys : List Value} {replacementSource source updated : Dynamic.Value} {replacement value : Value}
    {sourceType : TypeSystem.Ty} {nativeType : Ty} {steps : List PreparedStep} {projections : List Dynamic.EvaluatedProjection} {count : Nat}
    (tree : UpdateTree checked registry functions mapping world prepared keys replacementSource replacement sourceType source value nativeType steps projections updated count)
    {identities : Dynamic.Value → Word → Prop} (faithful : IdentityFaithful identities)
    (functionLeaves : FunctionObservations checked.catalog functions identities) (keyLength : prepared.keyTypes.length = keys.length)
    (environment : Environment) (store : Store) (type : Ty) (current keyExpression replacementExpression : Expr)
    (selected : Selects environment current value) (keysSelected : Selects environment keyExpression (packValues keys))
    (replacementSelected : Selects environment replacementExpression replacement) :
    ∃ native finalStore administrative,
      Dynamic.ProjectionsUpdate (fun _ value => value = replacementSource) (some source) projections updated ∧
      ValueRep checked registry functions mapping world sourceType updated native nativeType ∧
      Evaluates environment store (update prepared steps type current keyExpression replacementExpression) (.inRight .word native) finalStore ∧
      finalStore = store ++ administrative ∧ administrative.length = count := by
  induction tree generalizing environment store type current keyExpression replacementExpression with
  | leaf related => exact ⟨_, store, [], .leaf rfl, related, .inRight (replacementSelected.evaluates store), by simp, rfl⟩
  | compatible view _ ih =>
    obtain ⟨native, finalStore, administrative, updated, related, evaluated, appended, count⟩ :=
      ih environment store type current keyExpression replacementExpression selected keysSelected replacementSelected
    exact ⟨native, finalStore, administrative, updated, .compatible view related, evaluated, appended, count⟩
  | @member expected metadata tag id sources values types dataType index branches branch fieldType childType name sourceChild valueChild updatedChild steps projections count fields owner branchAt constructor branchTypes field fieldCore sourceAt coreAt tail ih =>
    have arity : branch.payloadTypes.length = values.length := branchTypes ▸ (fields.payloads.length.2.2.symm.trans fields.payloads.length.2.1)
    let payload := Value.pair (.word id) (packValues values)
    obtain ⟨child, finalStore, administrative, changed, related, evaluated, appended, counted⟩ :=
      ih (payload :: environment) store fieldType _ (shift 1 keyExpression) (shift 1 replacementExpression)
        (projectPacked_selects (.second (.var (index := 0) rfl)) arity index coreAt)
        (by simpa [shift] using keysSelected.weaken payload)
        (by simpa [shift] using replacementSelected.weaken payload)
    refine ⟨_, finalStore, administrative, .member sourceAt changed (replaceAt sourceAt updatedChild),
      (fields.replace field fieldCore related).represents,
      Evaluates.matchData (selected.evaluates store) owner (by simp only [List.getElem?_map, branchAt, Option.map_some]; rfl) ?_, appended, counted⟩
    apply LanguageResult.bind_success _ evaluated
    rw [constructor]
    exact .inRight (.construct (.pair (.first (.var rfl)) (replacePacked_evaluates arity (.second (.var rfl)) (.var rfl))))
  | @mapping sourceKey sourceValue index sources header entries fallback lookup key child updatedChild updatedEntries steps projections count certificate fields keyRep keyAt read tail inserted ih =>
    have keySelected := projectPacked_selects keysSelected keyLength index.keyPosition keyAt
    obtain ⟨result, meaning, evaluated⟩ := selectedIndex_meaning certificate prepared faithful functionLeaves fields keyRep
      environment store current keyExpression selected keySelected
    obtain ⟨native, rfl, related⟩ := read.payload meaning
    obtain ⟨changedNative, childStore, childCells, changed, childRep, childEvaluated, childAppended, childCounted⟩ :=
      ih native related (native :: environment) _ index.layout.valueType (.var 0) (shift 1 keyExpression) (shift 1 replacementExpression)
        (.var rfl) (by simpa [shift] using keysSelected.weaken native) (by simpa [shift] using replacementSelected.weaken native)
    let later := changedNative :: native :: environment
    obtain ⟨actualEntries, nativeEntries, actualInserted, represented, insertedEvaluation⟩ := insert_meaning certificate.comparison certificate.keyType faithful functionLeaves fields keyRep childRep
      later childStore (shift 2 current) (SourceCoreDataExpressions.projectPacked index.keyPosition prepared.keyTypes (shift 2 keyExpression)) (.var 0)
      (by simpa [shift, List.range_succ] using (selected.weaken native).weaken changedNative)
      (by simpa [shift, List.range_succ, projectPacked_weaken] using (keySelected.weaken native).weaken changedNative) (.var rfl)
    have same := actualInserted.functional inserted
    subst actualEntries
    obtain ⟨before, beforeAppended, beforeCount⟩ := Transport.lookupStore_extension certificate.comparison index.layout environment store header fallback entries key
    obtain ⟨after, afterAppended, afterCount⟩ := Transport.insertStore_extension certificate.comparison index.layout later childStore header fallback entries key changedNative
    refine ⟨_, Transport.insertStore certificate.comparison index.layout later childStore header fallback entries key changedNative,
      before ++ childCells ++ after, ?_, represented.represents,
      LanguageResult.bind_success _ evaluated (LanguageResult.bind_success _ childEvaluated ?_), ?_, ?_⟩
    · cases read with
      | found found => exact .indexFound found changed inserted
      | default absent defaulted => exact .indexDefault absent defaulted changed inserted
    · simpa only [certificate.expression] using insertedEvaluation
    · rw [afterAppended, childAppended, beforeAppended]
      simp only [List.append_assoc]
    · simp only [List.length_append, beforeCount, childCounted, afterCount]; omega

end Solcore.SourceSemantics.CoreLowering.CompatibleMapping.MixedPaths
