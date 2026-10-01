import Solcore.SourceSemantics.CoreLowering.CompatibleMappingPlaces

/-! Actual compatible updater/setter composition. Selection happens before
insertion, so a missing raw default prevents even a constant replacement.
No generated child execution is assumed by the whole-step theorems. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleMapping
open Core Frontend SourceInference CompatiblePayload CompatibleEquality DataEquality DataPatternValues
open SourceCoreCompatibleDataPlaces

inductive UpdateResult (checked : SourceCoreCompatibleCatalog.Checked) (registry : Registry)
    (functions : FunctionModel checked.catalog) (mapping : GeneralHeap.LocationMap) (world : StoreTyping)
    (sourceKey sourceValue : TypeSystem.Ty) (key replacement : Dynamic.Value) (sources : List (Dynamic.Value × Dynamic.Value))
    (header : Word) (layout : Core.OrderedMapping.Layout) (fallback : Option Value) (missingBase : Word) : Value → Nat → Prop where
  | updated {sources' entries}
      (inserted : Dynamic.MappingInsert key replacement sources sources')
      (updated : Dynamic.ProjectionsUpdate (fun _ value => value = replacement)
        (some (.mapping sourceKey sourceValue sources)) [.index key] (.mapping sourceKey sourceValue sources'))
      (represented : Fields checked registry functions mapping world sourceKey sourceValue sources' header layout entries fallback) :
      UpdateResult checked registry functions mapping world sourceKey sourceValue key replacement sources header layout fallback missingBase
        (.inRight .word (Transport.carrier header fallback layout entries)) (2 * (checked.catalog.entries.length + 1))
  | missing (absent : Dynamic.MappingAbsent key sources) (missing : ¬ Dynamic.Defaultable sourceValue) :
      UpdateResult checked registry functions mapping world sourceKey sourceValue key replacement sources header layout fallback missingBase
        (.inLeft (SourceCoreMappingWithDefault.type layout) (.word (missingBase.add header))) (checked.catalog.entries.length + 1)

 theorem ReadResult.update {checked : SourceCoreCompatibleCatalog.Checked} {registry : Registry}
    {functions : FunctionModel checked.catalog} {mapping : GeneralHeap.LocationMap} {world : StoreTyping}
    {sourceKey sourceValue : TypeSystem.Ty} {key replacement : Dynamic.Value} {sources sources' : List (Dynamic.Value × Dynamic.Value)}
    {valueType : Ty} {missingBase header : Word} {value : Value}
    (read : ReadResult checked registry functions mapping world sourceValue key sources valueType missingBase header (.inRight .word value))
    (inserted : Dynamic.MappingInsert key replacement sources sources') :
    Dynamic.ProjectionsUpdate (fun _ value => value = replacement) (some (.mapping sourceKey sourceValue sources))
      [.index key] (.mapping sourceKey sourceValue sources') := by
  cases read with
  | found found => exact .indexFound found (.leaf rfl) inserted
  | default absent defaulted => exact .indexDefault absent defaulted (.leaf rfl) inserted

private theorem update_after_read {checked : SourceCoreCompatibleCatalog.Checked} {index : PreparedIndex}
    (certificate : Index checked index) (prepared : Prepared)
    {registry : Registry} {functions : FunctionModel checked.catalog} {mapping : GeneralHeap.LocationMap} {world : StoreTyping}
    {identities : Dynamic.Value → Word → Prop} (faithful : IdentityFaithful identities)
    (functionLeaves : FunctionObservations checked.catalog functions identities)
    {sourceKey sourceValue : TypeSystem.Ty} {sources : List (Dynamic.Value × Dynamic.Value)}
    {header : Word} {entries : Core.OrderedMapping.Entries} {fallback : Option Value}
    (fields : Fields checked registry functions mapping world sourceKey sourceValue sources header index.layout entries fallback)
    {sourceLookup sourceReplacement : Dynamic.Value} {key replacement selected : Value}
    (keyRep : Payload registry functions mapping world sourceKey index.layout.keyType sourceLookup key)
    (replacementRep : Payload registry functions mapping world sourceValue index.layout.valueType sourceReplacement replacement)
    (read : ReadResult checked registry functions mapping world sourceValue sourceLookup sources index.layout.valueType index.missing header (.inRight .word selected))
    (environment : Environment) (store : Store) (current keys valueExpression : Expr)
    (mappingSelected : Selects environment current (Transport.carrier header fallback index.layout entries))
    (keySelected : Selects environment (SourceCoreDataExpressions.projectPacked index.keyPosition prepared.keyTypes keys) key)
    (valueSelected : Selects environment valueExpression replacement)
    (selection : Evaluates environment store (selectedIndex prepared index current keys) (.inRight .word selected)
      (Transport.lookupStore certificate.comparison index.layout environment store header fallback entries key)) :
    ∃ result finalStore administrative,
      UpdateResult checked registry functions mapping world sourceKey sourceValue sourceLookup sourceReplacement sources header index.layout fallback index.missing result
        (2 * (checked.catalog.entries.length + 1)) ∧
      Evaluates environment store (update prepared [.index index] (SourceCoreMappingWithDefault.type index.layout) current keys valueExpression) result finalStore ∧
      finalStore = store ++ administrative ∧ administrative.length = 2 * (checked.catalog.entries.length + 1) := by
  let middle := Transport.lookupStore certificate.comparison index.layout environment store header fallback entries key
  let later := replacement :: selected :: environment
  have shiftedKey : Selects later
      (SourceCoreDataExpressions.projectPacked index.keyPosition prepared.keyTypes (shift 2 keys)) key := by
    simpa [shift, List.range_succ, projectPacked_weaken] using (keySelected.weaken selected).weaken replacement
  obtain ⟨updated, nativeEntries, inserted, represented, evaluated⟩ := insert_meaning certificate.comparison certificate.keyType faithful functionLeaves
    fields keyRep replacementRep later middle (shift 2 current)
    (SourceCoreDataExpressions.projectPacked index.keyPosition prepared.keyTypes (shift 2 keys)) (.var 0)
    (by simpa [shift, List.range_succ] using (mappingSelected.weaken selected).weaken replacement) shiftedKey (.var rfl)
  obtain ⟨firstCells, firstAppended, firstLength⟩ := Transport.lookupStore_extension certificate.comparison index.layout
    environment store header fallback entries key
  obtain ⟨lastCells, lastAppended, lastLength⟩ := Transport.insertStore_extension certificate.comparison index.layout
    later middle header fallback entries key replacement
  refine ⟨_, Transport.insertStore certificate.comparison index.layout later middle header fallback entries key replacement, firstCells ++ lastCells, .updated inserted (read.update inserted) represented, ?_, ?_, ?_⟩
  · apply LanguageResult.bind_success _ selection
    apply LanguageResult.bind_success _ (.inRight (by simpa [shift, List.range_succ] using (valueSelected.weaken selected).evaluates middle))
    simpa only [certificate.expression] using evaluated
  · rw [lastAppended, show middle = store ++ firstCells from firstAppended, List.append_assoc]
  · simp only [List.length_append, firstLength, lastLength]; omega

 theorem updateOne_meaning {checked : SourceCoreCompatibleCatalog.Checked} {index : PreparedIndex}
    (certificate : Index checked index) (prepared : Prepared)
    {registry : Registry} {functions : FunctionModel checked.catalog} {mapping : GeneralHeap.LocationMap} {world : StoreTyping}
    {identities : Dynamic.Value → Word → Prop} (faithful : IdentityFaithful identities)
    (functionLeaves : FunctionObservations checked.catalog functions identities)
    {sourceKey sourceValue : TypeSystem.Ty} {sources : List (Dynamic.Value × Dynamic.Value)}
    {header : Word} {entries : Core.OrderedMapping.Entries} {fallback : Option Value}
    (fields : Fields checked registry functions mapping world sourceKey sourceValue sources header index.layout entries fallback)
    {sourceLookup sourceReplacement : Dynamic.Value} {key replacement : Value}
    (keyRep : Payload registry functions mapping world sourceKey index.layout.keyType sourceLookup key)
    (replacementRep : Payload registry functions mapping world sourceValue index.layout.valueType sourceReplacement replacement)
    (environment : Environment) (store : Store) (current keys valueExpression : Expr)
    (mappingSelected : Selects environment current (Transport.carrier header fallback index.layout entries))
    (keySelected : Selects environment (SourceCoreDataExpressions.projectPacked index.keyPosition prepared.keyTypes keys) key)
    (valueSelected : Selects environment valueExpression replacement) :
    ∃ result finalStore administrative count,
      UpdateResult checked registry functions mapping world sourceKey sourceValue sourceLookup sourceReplacement sources header index.layout fallback index.missing result count ∧
      Evaluates environment store (update prepared [.index index] (SourceCoreMappingWithDefault.type index.layout) current keys valueExpression) result finalStore ∧
      finalStore = store ++ administrative ∧ administrative.length = count := by
  obtain ⟨result, meaning, evaluated⟩ := selectedIndex_meaning certificate prepared faithful functionLeaves fields keyRep
    environment store current keys mappingSelected keySelected
  cases meaning with
  | found found represented =>
    obtain ⟨result, finalStore, administrative, meaning, evaluated, appended, length⟩ := update_after_read certificate prepared faithful functionLeaves fields
      keyRep replacementRep (.found found represented) environment store current keys valueExpression mappingSelected keySelected valueSelected evaluated
    exact ⟨result, finalStore, administrative, _, meaning, evaluated, appended, length⟩
  | default absent defaulted represented =>
    obtain ⟨result, finalStore, administrative, meaning, evaluated, appended, length⟩ := update_after_read certificate prepared faithful functionLeaves fields
      keyRep replacementRep (.default absent defaulted represented) environment store current keys valueExpression mappingSelected keySelected valueSelected evaluated
    exact ⟨result, finalStore, administrative, _, meaning, evaluated, appended, length⟩
  | missing absent missing =>
    obtain ⟨administrative, appended, length⟩ := Transport.lookupStore_extension certificate.comparison index.layout environment store header fallback entries key
    exact ⟨_, _, administrative, _, .missing absent missing, LanguageResult.bind_failure _ evaluated, appended, length⟩

 theorem setter_initialized {checked : SourceCoreCompatibleCatalog.Checked} {index : PreparedIndex}
    (certificate : Index checked index) (prepared : Prepared) (steps : prepared.steps = [.index index])
    (rootType : prepared.route.rootType = SourceCoreMappingWithDefault.type index.layout)
    {registry : Registry} {functions : FunctionModel checked.catalog} {mapping : GeneralHeap.LocationMap} {world : StoreTyping}
    {identities : Dynamic.Value → Word → Prop} (faithful : IdentityFaithful identities)
    (functionLeaves : FunctionObservations checked.catalog functions identities)
    {sourceKey sourceValue : TypeSystem.Ty} {sources : List (Dynamic.Value × Dynamic.Value)}
    {header : Word} {entries : Core.OrderedMapping.Entries} {fallback : Option Value}
    (fields : Fields checked registry functions mapping world sourceKey sourceValue sources header index.layout entries fallback)
    {sourceLookup sourceReplacement : Dynamic.Value} {key replacement : Value}
    (keyRep : Payload registry functions mapping world sourceKey index.layout.keyType sourceLookup key)
    (replacementRep : Payload registry functions mapping world sourceValue index.layout.valueType sourceReplacement replacement)
    (environment : Environment) (store : Store) (keyType : Ty) (keys : List Value) (argument : Expr)
    (keysLength : prepared.keyTypes.length = keys.length) (keyAt : keys[index.keyPosition]? = some key)
    (argumentSelected : Selects environment argument
      (.pair (.inRight .unit (Transport.carrier header fallback index.layout entries)) (.pair (packValues keys) replacement))) :
    ∃ result finalStore administrative count,
      UpdateResult checked registry functions mapping world sourceKey sourceValue sourceLookup sourceReplacement sources header index.layout fallback index.missing result count ∧
      Evaluates environment store (.apply (setter prepared keyType) argument) result finalStore ∧
      finalStore = store ++ administrative ∧ administrative.length = count := by
  let stored := Transport.carrier header fallback index.layout entries
  let input := Value.pair (.inRight .unit stored) (.pair (packValues keys) replacement)
  let bodyEnvironment := stored :: input :: environment
  have selectedKey : Selects bodyEnvironment
      (SourceCoreDataExpressions.projectPacked index.keyPosition prepared.keyTypes (.first (.second (.var 1)))) key :=
    projectPacked_selects (.first (.second (.var rfl))) keysLength _ keyAt
  obtain ⟨result, finalStore, administrative, count, meaning, evaluated, appended, length⟩ := updateOne_meaning certificate prepared faithful functionLeaves
    fields keyRep replacementRep bodyEnvironment store (.var 0) (.first (.second (.var 1))) (.second (.second (.var 1)))
    (.var rfl) selectedKey (.second (.second (.var rfl)))
  refine ⟨result, finalStore, administrative, count, meaning, ?_, appended, length⟩
  apply Evaluates.apply .lambda (argumentSelected.evaluates store)
  simp only [steps, rootType]
  exact .caseRight (normalizeRoot_initialized prepared (.first (.var rfl)) store) evaluated

end Solcore.SourceSemantics.CoreLowering.CompatibleMapping
