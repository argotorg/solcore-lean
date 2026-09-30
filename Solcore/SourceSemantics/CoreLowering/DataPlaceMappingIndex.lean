import Solcore.SourceSemantics.CoreLowering.DataMappingComparison
import Solcore.SourceSemantics.CoreLowering.DataPlaceMappingPreparation
import Solcore.SourceSemantics.Dynamic.Place

/-! Actual generated index selection, including its optional default and
missing-default fault. Source lookup/default relations are independent of Core
execution. The comparator and default supply their own finite evaluations. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataPlaceMappingIndex
open Core Frontend SourceInference SourceCoreDataPlaces DataEquality DataEqualityValues

structure Index (checked : SourceCoreDataCatalog.Checked) (sourceValue : TypeSystem.Ty) (index : PreparedIndex) where
  comparison : SourceCoreDataEquality.Prepared checked
  default : SourceCoreDefaultValue.Prepared checked
  comparisonExpression : index.comparison = comparison.expression
  defaultExpression : index.default = default.expression
  keyType : index.layout.keyType = comparison.type
  valueType : index.layout.valueType = default.type
  defaultSource : default.sourceType = sourceValue

def Index.of_generated {checked : SourceCoreDataCatalog.Checked} {fuel count : Nat}
    {sourceKey sourceValue : TypeSystem.Ty} {layout : Core.OrderedMapping.Layout} {key : ExpressionId} {missing : Word}
    {comparison : SourceCoreDataEquality.Prepared checked} {default : SourceCoreDefaultValue.Prepared checked}
    (comparisonGenerated : SourceCoreDataEquality.prepare fuel checked sourceKey = .ok comparison)
    (defaultGenerated : SourceCoreDefaultValue.prepare (sourceValue.size + 1) checked sourceValue = .ok default)
    (keyProjection : checked.catalog.project sourceKey = .ok layout.keyType)
    (valueProjection : checked.catalog.project sourceValue = .ok layout.valueType) :
    Index checked sourceValue ⟨layout, key, count, comparison.expression, default.expression, missing⟩ where
  comparison := comparison
  default := default
  comparisonExpression := rfl
  defaultExpression := rfl
  keyType := by
    have projected := comparison.projection
    rw [DataPlaceMappingPreparation.comparison_sourceType comparisonGenerated] at projected
    exact Except.ok.inj (keyProjection.symm.trans projected)
  valueType := by
    have projected := default.projection
    rw [DataPlaceMappingPreparation.default_sourceType defaultGenerated] at projected
    exact Except.ok.inj (valueProjection.symm.trans projected)
  defaultSource := DataPlaceMappingPreparation.default_sourceType defaultGenerated

inductive Reads (key : Dynamic.Value) (entries : List (Dynamic.Value × Dynamic.Value))
    (type : TypeSystem.Ty) (value : Dynamic.Value) : Prop where
  | found (lookup : Dynamic.MappingLookup key entries value) : Reads key entries type value
  | default (absent : Dynamic.MappingAbsent key entries) (valueDefault : Dynamic.DefaultValue type value) :
      Reads key entries type value

theorem Reads.projections {key value : Dynamic.Value} {entries : List (Dynamic.Value × Dynamic.Value)}
    {type : TypeSystem.Ty} (read : Reads key entries type value) (keyType : TypeSystem.Ty) :
    Dynamic.ProjectionsRead (some (.mapping keyType type entries)) [.index key] (some value) := by
  cases read with
  | found lookup => exact .indexFound lookup .nil
  | default absent valueDefault => exact .indexDefault absent valueDefault .nil

theorem Reads.update {key selected replacement : Dynamic.Value} {entries updated : List (Dynamic.Value × Dynamic.Value)}
    {type : TypeSystem.Ty} (read : Reads key entries type selected)
    (inserted : Dynamic.MappingInsert key replacement entries updated) (keyType : TypeSystem.Ty) :
    Dynamic.ProjectionsUpdate (fun _ value => value = replacement) (some (.mapping keyType type entries))
      [.index key] (.mapping keyType type updated) := by
  cases read with
  | found lookup => exact .indexFound lookup (.leaf rfl) inserted
  | default absent valueDefault => exact .indexDefault absent valueDefault (.leaf rfl) inserted

abbrev KeyRep {checked : SourceCoreDataCatalog.Checked} {sourceValue : TypeSystem.Ty} {index : PreparedIndex}
    (certificate : Index checked sourceValue index) (signatures : ProgramSignatures)
    (identities : Dynamic.Value → Word → Prop) := DataMappingComparison.KeyRep certificate.comparison signatures identities

def selectedStore {checked : SourceCoreDataCatalog.Checked} {sourceValue : TypeSystem.Ty} {index : PreparedIndex}
    (certificate : Index checked sourceValue index) (environment : Environment) (store : Store)
    (entries : Core.OrderedMapping.Entries) (key : Value) : Store :=
  DataMappingComparison.lookupStore certificate.comparison index.layout environment store entries key

theorem selectedIndex_found {checked : SourceCoreDataCatalog.Checked} {sourceValue : TypeSystem.Ty} {index : PreparedIndex}
    (certificate : Index checked sourceValue index) (prepared : Prepared)
    {signatures : ProgramSignatures} {identities : Dynamic.Value → Word → Prop}
    (faithful : IdentityFaithful identities) {valueRel : OrderedMapping.Relation}
    {sourceKey sourceSelected : Dynamic.Value} {key : Value}
    {sources : List (Dynamic.Value × Dynamic.Value)} {entries : Core.OrderedMapping.Entries}
    (keyRep : KeyRep certificate signatures identities sourceKey key)
    (related : OrderedMapping.EntriesRel (KeyRep certificate signatures identities) valueRel sources entries)
    (found : Dynamic.MappingLookup sourceKey sources sourceSelected)
    (environment : Environment) (store : Store) (current keys : Expr)
    (mappingSelected : Selects environment current (Core.OrderedMapping.encode index.layout entries))
    (keySelected : Selects environment (SourceCoreDataExpressions.projectPacked index.keyPosition prepared.keyTypes keys) key) :
    ∃ value, valueRel sourceSelected value ∧
      Evaluates environment store (selectedIndex prepared index current keys) (.inRight .word value)
        (selectedStore certificate environment store entries key) := by
  obtain ⟨value, represented, evaluated⟩ := DataMappingComparison.lookup_found certificate.comparison index.layout
    certificate.keyType faithful keyRep related found environment store current _ mappingSelected keySelected
  refine ⟨value, represented, ?_⟩
  unfold selectedIndex
  rw [certificate.comparisonExpression]
  exact LanguageResult.bind_success _ evaluated (.caseRight (.var rfl) (.inRight (.var rfl)))

theorem selectedIndex_default {checked : SourceCoreDataCatalog.Checked} {sourceValue : TypeSystem.Ty} {index : PreparedIndex}
    (certificate : Index checked sourceValue index) (prepared : Prepared)
    {signatures : ProgramSignatures} {identities : Dynamic.Value → Word → Prop}
    (faithful : IdentityFaithful identities) {valueRel : OrderedMapping.Relation}
    {sourceKey sourceDefault : Dynamic.Value} {key : Value}
    {sources : List (Dynamic.Value × Dynamic.Value)} {entries : Core.OrderedMapping.Entries}
    (keyRep : KeyRep certificate signatures identities sourceKey key)
    (related : OrderedMapping.EntriesRel (KeyRep certificate signatures identities) valueRel sources entries)
    (absent : Dynamic.MappingAbsent sourceKey sources) (defaulted : Dynamic.DefaultValue sourceValue sourceDefault)
    (environment : Environment) (store : Store) (current keys : Expr)
    (mappingSelected : Selects environment current (Core.OrderedMapping.encode index.layout entries))
    (keySelected : Selects environment (SourceCoreDataExpressions.projectPacked index.keyPosition prepared.keyTypes keys) key) :
    ∃ value expression, DataDefaults.Tree checked.catalog sourceValue sourceDefault value expression ∧
      Evaluates environment store (selectedIndex prepared index current keys) (.inRight .word value)
        (selectedStore certificate environment store entries key) := by
  have lookup := DataMappingComparison.lookup_absent certificate.comparison index.layout certificate.keyType faithful
    keyRep related absent environment store current _ mappingSelected keySelected
  obtain ⟨defaultValue, represented, defaultEvaluation⟩ := DataDefaults.prepared_preserves certificate.default
    (.unit :: .inLeft index.layout.valueType .unit :: environment) (selectedStore certificate environment store entries key)
  rw [certificate.defaultSource] at represented
  cases represented with
  | absent missing => exact False.elim (missing sourceDefault defaulted)
  | @present source value expression tree =>
    have same := tree.meaning.functional defaulted
    subst source
    refine ⟨value, expression, tree, ?_⟩
    unfold selectedIndex
    rw [certificate.comparisonExpression, certificate.defaultExpression]
    exact LanguageResult.bind_success _ lookup
      (.caseLeft (.var rfl) (.caseRight defaultEvaluation (.inRight (.var rfl))))

theorem selectedIndex_missing {checked : SourceCoreDataCatalog.Checked} {sourceValue : TypeSystem.Ty} {index : PreparedIndex}
    (certificate : Index checked sourceValue index) (prepared : Prepared)
    {signatures : ProgramSignatures} {identities : Dynamic.Value → Word → Prop}
    (faithful : IdentityFaithful identities) {valueRel : OrderedMapping.Relation}
    {sourceKey : Dynamic.Value} {key : Value}
    {sources : List (Dynamic.Value × Dynamic.Value)} {entries : Core.OrderedMapping.Entries}
    (keyRep : KeyRep certificate signatures identities sourceKey key)
    (related : OrderedMapping.EntriesRel (KeyRep certificate signatures identities) valueRel sources entries)
    (absent : Dynamic.MappingAbsent sourceKey sources) (missing : ¬ Dynamic.Defaultable sourceValue)
    (environment : Environment) (store : Store) (current keys : Expr)
    (mappingSelected : Selects environment current (Core.OrderedMapping.encode index.layout entries))
    (keySelected : Selects environment (SourceCoreDataExpressions.projectPacked index.keyPosition prepared.keyTypes keys) key) :
    Evaluates environment store (selectedIndex prepared index current keys) (.inLeft index.layout.valueType (.word index.missing))
      (selectedStore certificate environment store entries key) := by
  have lookup := DataMappingComparison.lookup_absent certificate.comparison index.layout certificate.keyType faithful
    keyRep related absent environment store current _ mappingSelected keySelected
  obtain ⟨defaultValue, represented, defaultEvaluation⟩ := DataDefaults.prepared_preserves certificate.default
    (.unit :: .inLeft index.layout.valueType .unit :: environment) (selectedStore certificate environment store entries key)
  rw [certificate.defaultSource] at represented
  cases represented with
  | present tree => exact False.elim (missing tree.meaning.defaultable)
  | absent =>
    unfold selectedIndex
    rw [certificate.comparisonExpression, certificate.defaultExpression]
    exact LanguageResult.bind_success _ lookup
      (.caseLeft (.var rfl) (.caseLeft defaultEvaluation (.inLeft .word)))

theorem selectedStore_extension {checked : SourceCoreDataCatalog.Checked} {sourceValue : TypeSystem.Ty} {index : PreparedIndex}
    (certificate : Index checked sourceValue index) (environment : Environment) (store : Store)
    (entries : Core.OrderedMapping.Entries) (key : Value) :
    ∃ administrative, selectedStore certificate environment store entries key = store ++ administrative ∧
      administrative.length = checked.catalog.entries.length + 1 :=
  DataMappingComparison.helper_store_extension certificate.comparison environment store _ _ _ _

theorem selectedIndex_preserves {checked : SourceCoreDataCatalog.Checked} {sourceValue : TypeSystem.Ty} {index : PreparedIndex}
    (certificate : Index checked sourceValue index) (prepared : Prepared)
    {signatures : ProgramSignatures} {identities : Dynamic.Value → Word → Prop}
    (faithful : IdentityFaithful identities) {valueRel : OrderedMapping.Relation}
    {sourceKey sourceSelected : Dynamic.Value} {key : Value}
    {sources : List (Dynamic.Value × Dynamic.Value)} {entries : Core.OrderedMapping.Entries}
    (keyRep : KeyRep certificate signatures identities sourceKey key)
    (related : OrderedMapping.EntriesRel (KeyRep certificate signatures identities) valueRel sources entries)
    (read : Reads sourceKey sources sourceValue sourceSelected)
    (environment : Environment) (store : Store) (current keys : Expr)
    (mappingSelected : Selects environment current (Core.OrderedMapping.encode index.layout entries))
    (keySelected : Selects environment (SourceCoreDataExpressions.projectPacked index.keyPosition prepared.keyTypes keys) key) :
    ∃ value, (valueRel sourceSelected value ∨ ∃ expression, DataDefaults.Tree checked.catalog sourceValue sourceSelected value expression) ∧
      Evaluates environment store (selectedIndex prepared index current keys) (.inRight .word value)
        (selectedStore certificate environment store entries key) := by
  cases read with
  | found lookup =>
    obtain ⟨value, related, evaluated⟩ := selectedIndex_found certificate prepared faithful keyRep related lookup
      environment store current keys mappingSelected keySelected
    exact ⟨value, .inl related, evaluated⟩
  | default absent valueDefault =>
    obtain ⟨value, expression, represented, evaluated⟩ := selectedIndex_default certificate prepared faithful keyRep related
      absent valueDefault environment store current keys mappingSelected keySelected
    exact ⟨value, .inr ⟨expression, represented⟩, evaluated⟩

/-- A real single-index preparation supplies the comparator/default certificate.
The two projection equations authenticate its declared layout, separately from
the preparation loop, which only reads the catalog key type. -/
theorem single_index_of_prepare {checked : SourceCoreDataCatalog.Checked} {fuel : Nat}
    {route : Route} {prepared : Prepared} {invalid : Word} {missing : TypeSystem.Ty → Word}
    {layout : Core.OrderedMapping.Layout} {key : ExpressionId} {sourceKey sourceValue registeredValue : TypeSystem.Ty}
    {entry : SourceCoreDataCatalog.Entry}
    (accepted : prepare checked fuel route invalid missing = .ok prepared)
    (routeSteps : route.steps = [.index layout key sourceValue])
    (selected : checked.catalog.entries[layout.dataType.index]? = some entry)
    (mappingType : entry.sourceType = .mapping sourceKey registeredValue)
    (keyProjection : checked.catalog.project sourceKey = .ok layout.keyType)
    (valueProjection : checked.catalog.project sourceValue = .ok layout.valueType) :
    ∃ index, Nonempty (Index checked sourceValue index) ∧ prepared.steps = [.index index] ∧
      prepared.keys = [(key, layout.keyType)] ∧ index.layout = layout ∧ index.keyPosition = 0 ∧
      index.missing = missing sourceValue := by
  rcases prepared with ⟨preparedRoute, preparedSteps, preparedKeys, preparedInvalid⟩
  obtain ⟨_, _, generated⟩ := DataPlaceMappingPreparation.steps_of_prepare accepted
  rw [routeSteps] at generated
  cases generated with
  | index selected' mappingType' comparisonGenerated defaultGenerated tail =>
    have sameEntry := Option.some.inj (selected'.symm.trans selected)
    subst sameEntry
    have sameTypes := mappingType'.symm.trans mappingType
    cases sameTypes
    cases tail
    exact ⟨_, ⟨Index.of_generated comparisonGenerated defaultGenerated keyProjection valueProjection⟩,
      rfl, rfl, rfl, rfl, rfl⟩

end Solcore.SourceSemantics.CoreLowering.DataPlaceMappingIndex
