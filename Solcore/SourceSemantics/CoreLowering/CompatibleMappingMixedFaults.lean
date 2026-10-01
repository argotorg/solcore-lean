import Solcore.SourceSemantics.CoreLowering.CompatibleMappingMixedPaths

/-! The first unavailable raw mapping default stops both mixed selectors and
updaters. Exact raw key-type guards belong to independent source fault typing;
the ordinary helpers do not implement an extra key-type check. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleMapping.MixedPaths
open Core Frontend SourceInference CompatiblePayload CompatibleEquality DataEquality DataPatternValues
open SourceCoreCompatibleDataPlaces

inductive FaultTree (checked : SourceCoreCompatibleCatalog.Checked) (registry : Registry)
    {ambient : AmbientDefinitions checked.catalog.definitions}
    (functions : FunctionModel checked.catalog ambient) (mapping : GeneralHeap.LocationMap) (world : StoreTyping)
    (prepared : Prepared) (keys : List Value) :
    Dynamic.Value → Value → Ty → List PreparedStep → List Dynamic.EvaluatedProjection → Dynamic.SemanticFault → Word → Nat → Prop where
  | missing {sourceKey sourceValue index sources header entries fallback lookup key steps projections}
      (certificate : Index checked index)
      (fields : Fields checked registry functions mapping world sourceKey sourceValue sources header index.layout entries fallback)
      (keyRep : Payload registry functions mapping world sourceKey index.layout.keyType lookup key)
      (keyTyped : Dynamic.ValueRuntimeTypeMatches lookup sourceKey) (keyAt : keys[index.keyPosition]? = some key)
      (absent : Dynamic.MappingAbsent lookup sources) (unavailable : ¬ Dynamic.Defaultable sourceValue) :
      FaultTree checked registry functions mapping world prepared keys
        (.mapping sourceKey sourceValue sources) (Transport.carrier header fallback index.layout entries) (SourceCoreMappingWithDefault.type index.layout)
        (.index index :: steps) (.index lookup :: projections) (.missingMappingDefault sourceValue) (index.missing.add header)
        (checked.catalog.entries.length + 1)
  | member {expected metadata tag id sources values types dataType index branches branch fieldType childType name}
      {sourceChild valueChild steps projections reason token count}
      (fields : ConstructorFields checked registry functions mapping world expected metadata tag id sources values types)
      (owner : tag.owner = dataType) (branchAt : branches[tag.index]? = some branch)
      (branchTypes : branch.payloadTypes = types)
      (field : metadata.payloadTypes[index]? = some childType) (fieldCore : types[index]? = some fieldType)
      (sourceAt : Dynamic.ValueAt sources index sourceChild) (coreAt : values[index]? = some valueChild)
      (tail : FaultTree checked registry functions mapping world prepared keys sourceChild valueChild fieldType steps projections reason token count) :
      FaultTree checked registry functions mapping world prepared keys
        (.constructed metadata sources) (.constructed tag (.pair (.word id) (packValues values))) (.namedData dataType)
        (.member dataType index branches fieldType :: steps) (.member name index :: projections) reason token count
  | mapping {sourceKey sourceValue index sources header entries fallback lookup key child steps projections reason token count}
      (certificate : Index checked index)
      (fields : Fields checked registry functions mapping world sourceKey sourceValue sources header index.layout entries fallback)
      (keyRep : Payload registry functions mapping world sourceKey index.layout.keyType lookup key)
      (keyTyped : Dynamic.ValueRuntimeTypeMatches lookup sourceKey) (keyAt : keys[index.keyPosition]? = some key)
      (selected : Selected lookup sources sourceValue child)
      (tail : ∀ value, Payload registry functions mapping world sourceValue index.layout.valueType child value →
        FaultTree checked registry functions mapping world prepared keys child value index.layout.valueType steps projections reason token count) :
      FaultTree checked registry functions mapping world prepared keys
        (.mapping sourceKey sourceValue sources) (Transport.carrier header fallback index.layout entries) (SourceCoreMappingWithDefault.type index.layout)
        (.index index :: steps) (.index lookup :: projections) reason token (checked.catalog.entries.length + 1 + count)

 theorem FaultTree.preserves {checked : SourceCoreCompatibleCatalog.Checked} {registry : Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {mapping : GeneralHeap.LocationMap} {world : StoreTyping}
    {prepared : Prepared} {keys : List Value} {source : Dynamic.Value} {value : Value} {type : Ty}
    {steps : List PreparedStep} {projections : List Dynamic.EvaluatedProjection} {reason : Dynamic.SemanticFault} {token : Word} {count : Nat}
    (tree : FaultTree checked registry functions mapping world prepared keys source value type steps projections reason token count)
    {identities : Dynamic.Value → Word → Prop} (faithful : IdentityFaithful identities)
    (functionLeaves : FunctionObservations checked.catalog functions identities) (keyLength : prepared.keyTypes.length = keys.length)
    (environment : Environment) (store : Store) (current keyExpression replacement : Expr)
    (selected : Selects environment current value) (keysSelected : Selects environment keyExpression (packValues keys)) :
    ∃ finalStore administrative,
      Dynamic.ProjectionsFaults (some source) projections reason ∧
      Evaluates environment store (select prepared steps current keyExpression) (.inLeft prepared.optionalLeaf (.word token)) finalStore ∧
      Evaluates environment store (update prepared steps type current keyExpression replacement) (.inLeft type (.word token)) finalStore ∧
      finalStore = store ++ administrative ∧ administrative.length = count := by
  induction tree generalizing environment store current keyExpression replacement with
  | @missing sourceKey sourceValue index sources header entries fallback lookup key steps projections certificate fields keyRep keyTyped keyAt absent unavailable =>
    obtain ⟨result, meaning, evaluated⟩ := selectedIndex_meaning certificate prepared faithful functionLeaves fields keyRep
      environment store current keyExpression selected (projectPacked_selects keysSelected keyLength index.keyPosition keyAt)
    have result : result = .inLeft index.layout.valueType (.word (index.missing.add header)) := by
      cases meaning with
      | found found _ => exact (absent.excludes_lookup found).elim
      | default _ defaulted _ => exact (unavailable defaulted.defaultable).elim
      | missing => rfl
    subst result
    obtain ⟨administrative, appended, counted⟩ := Transport.lookupStore_extension certificate.comparison index.layout environment store header fallback entries key
    exact ⟨_, administrative, .indexDefaultUnavailable keyTyped absent unavailable,
      LanguageResult.bind_failure _ evaluated, LanguageResult.bind_failure _ evaluated, appended, counted⟩
  | @member expected metadata tag id sources values types dataType index branches branch fieldType childType name sourceChild valueChild steps projections reason token count fields owner branchAt branchTypes field fieldCore sourceAt coreAt tail ih =>
    have arity : branch.payloadTypes.length = values.length := branchTypes ▸ (fields.payloads.length.2.2.symm.trans fields.payloads.length.2.1)
    let payload := Value.pair (.word id) (packValues values)
    obtain ⟨finalStore, administrative, fault, readEvaluation, updateEvaluation, appended, counted⟩ :=
      ih (payload :: environment) store _ (shift 1 keyExpression) (shift 1 replacement)
        (projectPacked_selects (.second (.var (index := 0) rfl)) arity index coreAt)
        (by simpa [shift] using keysSelected.weaken payload)
    refine ⟨finalStore, administrative, .member sourceAt fault, ?_, ?_, appended, counted⟩
    · exact .matchData (selected.evaluates store) owner
        (by simp only [List.getElem?_map, branchAt, Option.map_some] <;> rfl) readEvaluation
    · exact .matchData (selected.evaluates store) owner
        (by simp only [List.getElem?_map, branchAt, Option.map_some] <;> rfl) (LanguageResult.bind_failure _ updateEvaluation)
  | @mapping sourceKey sourceValue index sources header entries fallback lookup key child steps projections reason token count certificate fields keyRep keyTyped keyAt read tail ih =>
    obtain ⟨result, meaning, evaluated⟩ := selectedIndex_meaning certificate prepared faithful functionLeaves fields keyRep
      environment store current keyExpression selected (projectPacked_selects keysSelected keyLength index.keyPosition keyAt)
    obtain ⟨native, rfl, related⟩ := read.payload meaning
    obtain ⟨finalStore, after, fault, readEvaluation, updateEvaluation, appended, counted⟩ :=
      ih native related (native :: environment) _ (.var 0) (shift 1 keyExpression) (shift 1 replacement) (.var rfl)
        (by simpa [shift] using keysSelected.weaken native)
    obtain ⟨before, beforeAppended, beforeCount⟩ := Transport.lookupStore_extension certificate.comparison index.layout environment store header fallback entries key
    refine ⟨finalStore, before ++ after, ?_, LanguageResult.bind_success _ evaluated readEvaluation,
      LanguageResult.bind_success _ evaluated (LanguageResult.bind_failure _ updateEvaluation), ?_, ?_⟩
    · cases read with
      | found found => exact .indexFound keyTyped found fault
      | default absent defaulted => exact .indexDefault keyTyped absent defaulted fault
    · rw [appended, beforeAppended, List.append_assoc]
    · simp only [List.length_append, beforeCount, counted]

end Solcore.SourceSemantics.CoreLowering.CompatibleMapping.MixedPaths
