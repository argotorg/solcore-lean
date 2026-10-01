import Solcore.SourceSemantics.CoreLowering.CompatibleMappingView
import Solcore.SourceSemantics.CoreLowering.CompatibleMappingExecution
import Solcore.SourceSemantics.Dynamic.Place

/-! Source meaning of actual compatible mapping wrappers. Lookup selects the
first equivalent entry, then the original raw value type's transported default,
then an exact header-specific missing token. Insertion retains full payload
receipts and ordered duplicates. This value-level library has no key-type guard. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleMapping
open Core Frontend CompatiblePayload CompatibleEquality DataEquality

inductive ReadResult (checked : SourceCoreCompatibleCatalog.Checked) (registry : Registry)
    {ambient : AmbientDefinitions checked.catalog.definitions}
    (functions : FunctionModel checked.catalog ambient) (mapping : GeneralHeap.LocationMap) (world : StoreTyping)
    (sourceValue : TypeSystem.Ty) (key : Dynamic.Value) (sources : List (Dynamic.Value × Dynamic.Value))
    (valueType : Ty) (missingBase header : Word) : Value → Prop where
  | found {source value}
      (lookup : Dynamic.MappingLookup key sources source)
      (represented : Payload registry functions mapping world sourceValue valueType source value) :
      ReadResult checked registry functions mapping world sourceValue key sources valueType missingBase header (.inRight .word value)
  | default {source value}
      (absent : Dynamic.MappingAbsent key sources) (defaulted : Dynamic.DefaultValue sourceValue source)
      (represented : Payload registry functions mapping world sourceValue valueType source value) :
      ReadResult checked registry functions mapping world sourceValue key sources valueType missingBase header (.inRight .word value)
  | missing (absent : Dynamic.MappingAbsent key sources) (missing : ¬ Dynamic.Defaultable sourceValue) :
      ReadResult checked registry functions mapping world sourceValue key sources valueType missingBase header
        (.inLeft valueType (.word (missingBase.add header)))

variable {checked : SourceCoreCompatibleCatalog.Checked} {registry : Registry}
  {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {mapping : GeneralHeap.LocationMap} {world : StoreTyping}
  {sourceKey sourceValue : TypeSystem.Ty} {sources : List (Dynamic.Value × Dynamic.Value)}
  {header : Word} {layout : Core.OrderedMapping.Layout} {entries : Core.OrderedMapping.Entries} {fallback : Option Value}

 theorem ReadResult.success {key : Dynamic.Value} {valueType : Ty} {missingBase header : Word} {value : Value}
    (result : ReadResult checked registry functions mapping world sourceValue key sources valueType missingBase header (.inRight .word value)) :
    ∃ source, Dynamic.ProjectionsRead (some (.mapping sourceKey sourceValue sources)) [.index key] (some source) ∧
      Payload registry functions mapping world sourceValue valueType source value := by
  cases result with
  | found found represented => exact ⟨_, .indexFound found .nil, represented⟩
  | default absent defaulted represented => exact ⟨_, .indexDefault absent defaulted .nil, represented⟩

/-- Source runtime compatibility is supplied separately. Native projection alone
cannot establish the metadata-derived key guard for runtime-compatible aliases. -/
 theorem ReadResult.failure {key : Dynamic.Value} {valueType : Ty} {missingBase header token : Word}
    (result : ReadResult checked registry functions mapping world sourceValue key sources valueType missingBase header (.inLeft valueType (.word token)))
    (keyTyped : Dynamic.ValueRuntimeTypeMatches key sourceKey) :
    token = missingBase.add header ∧ Dynamic.ProjectionsFaults (some (.mapping sourceKey sourceValue sources))
      [.index key] (.missingMappingDefault sourceValue) := by
  cases result with
  | missing absent missing => exact ⟨rfl, .indexDefaultUnavailable keyTyped absent missing⟩

 theorem lookup_meaning (prepared : SourceCoreCompatibleDataEquality.Prepared checked)
    (keyType : layout.keyType = prepared.type)
    {identities : Dynamic.Value → Word → Prop} (faithful : IdentityFaithful identities)
    (functionLeaves : FunctionObservations checked.catalog functions identities)
    (fields : Fields checked registry functions mapping world sourceKey sourceValue sources header layout entries fallback)
    {sourceLookup : Dynamic.Value} {key : Value}
    (keyRep : Payload registry functions mapping world sourceKey layout.keyType sourceLookup key)
    (environment : Environment) (store : Store) (missingBase : Word) (mappingExpression keyExpression : Expr)
    (mappingSelected : Selects environment mappingExpression (Transport.carrier header fallback layout entries))
    (keySelected : Selects environment keyExpression key) :
    ∃ result, ReadResult checked registry functions mapping world sourceValue sourceLookup sources layout.valueType missingBase header result ∧
      Evaluates environment store (SourceCoreMappingWithDefault.lookup layout missingBase prepared.expression mappingExpression keyExpression) result
        (Transport.lookupStore prepared layout environment store header fallback entries key) := by
  obtain ⟨equal, correct⟩ := CompatibleMappingComparison.exists_predicate_correct prepared registry faithful
  have fullCorrect := predicate_correct prepared functionLeaves keyType (sourceKey := sourceKey) (mapping := mapping) (world := world) correct
  have observedKey : CompatibleMappingComparison.KeyRep prepared registry identities sourceLookup key := by
    have observed := CompatibleEquality.ValueRep.observation functionLeaves keyRep
    simpa only [keyType] using observed
  have evaluated := Transport.lookup_evaluates prepared layout keyType faithful equal correct observedKey
    (entries_observed prepared functionLeaves keyType fields.stored) environment store missingBase header fallback
    mappingExpression keyExpression mappingSelected keySelected
  obtain ⟨found, sourceLookup⟩ := lookup_total sourceLookup sources
  cases sourceLookup with
  | found found =>
    obtain ⟨value, located, represented⟩ := lookup_preserves fullCorrect keyRep fields.stored found
    exact ⟨_, .found found represented, by simpa only [located, SourceCoreMappingWithDefault.selectedValue, Option.or] using evaluated⟩
  | absent absent =>
    have missing := OrderedMapping.absent_related fullCorrect keyRep (entries_related fields.stored) absent
    rw [missing] at evaluated
    cases fields.default with
    | absent noDefault projected wf =>
      exact ⟨_, .missing absent noDefault, evaluated⟩
    | present defaulted represented =>
      exact ⟨_, .default absent defaulted represented, evaluated⟩

 theorem lookup_run (prepared : SourceCoreCompatibleDataEquality.Prepared checked)
    (keyType : layout.keyType = prepared.type)
    {identities : Dynamic.Value → Word → Prop} (faithful : IdentityFaithful identities)
    (functionLeaves : FunctionObservations checked.catalog functions identities)
    (fields : Fields checked registry functions mapping world sourceKey sourceValue sources header layout entries fallback)
    {sourceLookup : Dynamic.Value} {key : Value}
    (keyRep : Payload registry functions mapping world sourceKey layout.keyType sourceLookup key)
    (environment : Environment) (store : Store) (missingBase : Word) (mappingExpression keyExpression : Expr)
    (mappingSelected : Selects environment mappingExpression (Transport.carrier header fallback layout entries))
    (keySelected : Selects environment keyExpression key) :
    ∃ result, ReadResult checked registry functions mapping world sourceValue sourceLookup sources layout.valueType missingBase header result ∧
      (∃ required, ∀ fuel, required ≤ fuel → runStateful fuel
        (.initial (SourceCoreMappingWithDefault.lookup layout missingBase prepared.expression mappingExpression keyExpression) environment store) =
          .done result (Transport.lookupStore prepared layout environment store header fallback entries key)) ∧
      (∀ fuel actual actualStore, runStateful fuel
        (.initial (SourceCoreMappingWithDefault.lookup layout missingBase prepared.expression mappingExpression keyExpression) environment store) = .done actual actualStore →
          actual = result ∧ actualStore = Transport.lookupStore prepared layout environment store header fallback entries key) := by
  obtain ⟨result, meaning, evaluated⟩ := lookup_meaning prepared keyType faithful functionLeaves fields keyRep environment store missingBase
    mappingExpression keyExpression mappingSelected keySelected
  exact ⟨result, meaning, evaluation_runStateful_complete_with_sufficient_fuel evaluated,
    fun _ _ _ ran => evaluation_deterministic (runStateful_evaluation_sound ran) evaluated⟩

 theorem insert_meaning (prepared : SourceCoreCompatibleDataEquality.Prepared checked)
    (keyType : layout.keyType = prepared.type)
    {identities : Dynamic.Value → Word → Prop} (faithful : IdentityFaithful identities)
    (functionLeaves : FunctionObservations checked.catalog functions identities)
    (fields : Fields checked registry functions mapping world sourceKey sourceValue sources header layout entries fallback)
    {sourceLookup sourceReplacement : Dynamic.Value} {key replacement : Value}
    (keyRep : Payload registry functions mapping world sourceKey layout.keyType sourceLookup key)
    (replacementRep : Payload registry functions mapping world sourceValue layout.valueType sourceReplacement replacement)
    (environment : Environment) (store : Store) (mappingExpression keyExpression valueExpression : Expr)
    (mappingSelected : Selects environment mappingExpression (Transport.carrier header fallback layout entries))
    (keySelected : Selects environment keyExpression key) (valueSelected : Selects environment valueExpression replacement) :
    ∃ updated nativeEntries,
      Dynamic.MappingInsert sourceLookup sourceReplacement sources updated ∧
      Fields checked registry functions mapping world sourceKey sourceValue updated header layout nativeEntries fallback ∧
      Evaluates environment store (SourceCoreMappingWithDefault.insert layout prepared.expression mappingExpression keyExpression valueExpression)
        (.inRight .word (Transport.carrier header fallback layout nativeEntries))
        (Transport.insertStore prepared layout environment store header fallback entries key replacement) := by
  obtain ⟨equal, correct⟩ := CompatibleMappingComparison.exists_predicate_correct prepared registry faithful
  have fullCorrect := predicate_correct prepared functionLeaves keyType (sourceKey := sourceKey) (mapping := mapping) (world := world) correct
  have observedKey : CompatibleMappingComparison.KeyRep prepared registry identities sourceLookup key := by
    have observed := CompatibleEquality.ValueRep.observation functionLeaves keyRep
    simpa only [keyType] using observed
  obtain ⟨updated, inserted⟩ := insert_total sourceLookup sourceReplacement sources
  have updatedRep := insert_preserves fullCorrect keyRep replacementRep fields.stored inserted
  refine ⟨updated, _, inserted,
    ⟨fields.metadata, fields.identity, fields.keyProjection, fields.valueProjection, fields.registered, updatedRep, fields.default⟩, ?_⟩
  exact Transport.insert_evaluates prepared layout keyType faithful equal correct observedKey
    (entries_observed prepared functionLeaves keyType fields.stored) environment store header fallback
    mappingExpression keyExpression valueExpression mappingSelected keySelected valueSelected

 theorem insert_run (prepared : SourceCoreCompatibleDataEquality.Prepared checked)
    (keyType : layout.keyType = prepared.type)
    {identities : Dynamic.Value → Word → Prop} (faithful : IdentityFaithful identities)
    (functionLeaves : FunctionObservations checked.catalog functions identities)
    (fields : Fields checked registry functions mapping world sourceKey sourceValue sources header layout entries fallback)
    {sourceLookup sourceReplacement : Dynamic.Value} {key replacement : Value}
    (keyRep : Payload registry functions mapping world sourceKey layout.keyType sourceLookup key)
    (replacementRep : Payload registry functions mapping world sourceValue layout.valueType sourceReplacement replacement)
    (environment : Environment) (store : Store) (mappingExpression keyExpression valueExpression : Expr)
    (mappingSelected : Selects environment mappingExpression (Transport.carrier header fallback layout entries))
    (keySelected : Selects environment keyExpression key) (valueSelected : Selects environment valueExpression replacement) :
    ∃ updated nativeEntries,
      Dynamic.MappingInsert sourceLookup sourceReplacement sources updated ∧
      Fields checked registry functions mapping world sourceKey sourceValue updated header layout nativeEntries fallback ∧
      (∃ required, ∀ fuel, required ≤ fuel → runStateful fuel
        (.initial (SourceCoreMappingWithDefault.insert layout prepared.expression mappingExpression keyExpression valueExpression) environment store) =
          .done (.inRight .word (Transport.carrier header fallback layout nativeEntries))
            (Transport.insertStore prepared layout environment store header fallback entries key replacement)) ∧
      (∀ fuel actual actualStore, runStateful fuel
        (.initial (SourceCoreMappingWithDefault.insert layout prepared.expression mappingExpression keyExpression valueExpression) environment store) = .done actual actualStore →
          actual = .inRight .word (Transport.carrier header fallback layout nativeEntries) ∧
          actualStore = Transport.insertStore prepared layout environment store header fallback entries key replacement) := by
  obtain ⟨updated, nativeEntries, inserted, fields, evaluated⟩ := insert_meaning prepared keyType faithful functionLeaves fields keyRep replacementRep
    environment store mappingExpression keyExpression valueExpression mappingSelected keySelected valueSelected
  exact ⟨updated, nativeEntries, inserted, fields, evaluation_runStateful_complete_with_sufficient_fuel evaluated,
    fun _ _ _ ran => evaluation_deterministic (runStateful_evaluation_sound ran) evaluated⟩

end Solcore.SourceSemantics.CoreLowering.CompatibleMapping
