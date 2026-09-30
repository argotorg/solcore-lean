import Solcore.SourceSemantics.CoreLowering.DataPlaceMappingIndex
import Solcore.SourceSemantics.CoreLowering.DataMappingHeap

/-! One generated mapping path step, including reconstruction of the latest
root. Comparators/defaults are evaluated from their actual preparation receipts.
The source mapping list remains ordered and duplicate keys are preserved. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataPlaceMappingPath
open Core Frontend SourceInference SourceCoreDataPlaces DataEquality DataPlaceMappingIndex

private theorem projectPacked_weaken (types : List Ty) (index : Nat) (expression : Expr) :
    SourceCoreDataExpressions.projectPacked index types (expression.weakenAt 0) =
      (SourceCoreDataExpressions.projectPacked index types expression).weakenAt 0 := by
  induction types generalizing index expression with
  | nil => simp [SourceCoreDataExpressions.projectPacked, Expr.weakenAt]
  | cons head tail ih => cases tail with
    | nil => rfl
    | cons next rest =>
      by_cases zero : index = 0
      · simp [SourceCoreDataExpressions.projectPacked, zero, Expr.weakenAt]
      · simpa [SourceCoreDataExpressions.projectPacked, zero, Expr.weakenAt] using ih (index - 1) (.second expression)

theorem select_found {checked : SourceCoreDataCatalog.Checked} {sourceValue : TypeSystem.Ty} {index : PreparedIndex}
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
      Evaluates environment store (select prepared [.index index] current keys) (.inRight .word (.inRight .unit value))
        (selectedStore certificate environment store entries key) := by
  obtain ⟨value, represented, evaluated⟩ := selectedIndex_found certificate prepared faithful keyRep related found
    environment store current keys mappingSelected keySelected
  exact ⟨value, represented, LanguageResult.bind_success _ evaluated (.inRight (.inRight (.var rfl)))⟩

theorem select_default {checked : SourceCoreDataCatalog.Checked} {sourceValue : TypeSystem.Ty} {index : PreparedIndex}
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
      Evaluates environment store (select prepared [.index index] current keys) (.inRight .word (.inRight .unit value))
        (selectedStore certificate environment store entries key) := by
  obtain ⟨value, expression, represented, evaluated⟩ := selectedIndex_default certificate prepared faithful keyRep related
    absent defaulted environment store current keys mappingSelected keySelected
  exact ⟨value, expression, represented, LanguageResult.bind_success _ evaluated (.inRight (.inRight (.var rfl)))⟩

theorem update_after_selection {checked : SourceCoreDataCatalog.Checked} {sourceValue : TypeSystem.Ty} {index : PreparedIndex}
    (certificate : Index checked sourceValue index) (prepared : Prepared)
    {signatures : ProgramSignatures} {identities : Dynamic.Value → Word → Prop}
    (faithful : IdentityFaithful identities) {valueRel : OrderedMapping.Relation}
    {sourceKey sourceReplacement : Dynamic.Value} {key replacement : Value}
    {sources updated : List (Dynamic.Value × Dynamic.Value)} {entries : Core.OrderedMapping.Entries}
    (keyRep : KeyRep certificate signatures identities sourceKey key) (replacementRep : valueRel sourceReplacement replacement)
    (related : OrderedMapping.EntriesRel (KeyRep certificate signatures identities) valueRel sources entries)
    (inserted : Dynamic.MappingInsert sourceKey sourceReplacement sources updated)
    (environment : Environment) (store middle : Store) (current keys replacementExpression : Expr)
    (mappingSelected : Selects environment current (Core.OrderedMapping.encode index.layout entries))
    (keySelected : Selects environment (SourceCoreDataExpressions.projectPacked index.keyPosition prepared.keyTypes keys) key)
    (replacementSelected : Selects environment replacementExpression replacement)
    {selected : Value}
    (selection : Evaluates environment store (selectedIndex prepared index current keys) (.inRight .word selected) middle) :
    ∃ output, OrderedMapping.ValueRel index.layout (KeyRep certificate signatures identities) valueRel updated output ∧
      Evaluates environment store (update prepared [.index index] index.layout.type current keys replacementExpression)
        (.inRight .word output)
        (DataMappingComparison.insertStore certificate.comparison index.layout (replacement :: selected :: environment)
          middle entries key replacement) := by
  have shiftedKey : Selects (replacement :: selected :: environment)
      (SourceCoreDataExpressions.projectPacked index.keyPosition prepared.keyTypes (shift 2 keys)) key := by
    simpa [shift, List.range_succ, projectPacked_weaken] using (keySelected.weaken selected).weaken replacement
  obtain ⟨output, represented, evaluated⟩ := DataMappingComparison.insert_preserves certificate.comparison index.layout
    certificate.keyType faithful keyRep replacementRep related inserted (replacement :: selected :: environment) middle
    (shift 2 current) _ (.var 0)
    (by simpa [shift, List.range_succ] using (mappingSelected.weaken selected).weaken replacement) shiftedKey (.var rfl)
  refine ⟨output, represented, LanguageResult.bind_success _ selection ?_⟩
  apply LanguageResult.bind_success _ (.inRight (by simpa [shift, List.range_succ] using (replacementSelected.weaken selected).evaluates middle))
  simpa only [certificate.comparisonExpression] using evaluated

theorem update_found {checked : SourceCoreDataCatalog.Checked} {sourceValue : TypeSystem.Ty} {index : PreparedIndex}
    (certificate : Index checked sourceValue index) (prepared : Prepared)
    {signatures : ProgramSignatures} {identities : Dynamic.Value → Word → Prop}
    (faithful : IdentityFaithful identities) {valueRel : OrderedMapping.Relation}
    {sourceKey sourceSelected sourceReplacement : Dynamic.Value} {key replacement : Value}
    {sources updated : List (Dynamic.Value × Dynamic.Value)} {entries : Core.OrderedMapping.Entries}
    (keyRep : KeyRep certificate signatures identities sourceKey key) (replacementRep : valueRel sourceReplacement replacement)
    (related : OrderedMapping.EntriesRel (KeyRep certificate signatures identities) valueRel sources entries)
    (found : Dynamic.MappingLookup sourceKey sources sourceSelected)
    (inserted : Dynamic.MappingInsert sourceKey sourceReplacement sources updated)
    (environment : Environment) (store : Store) (current keys replacementExpression : Expr)
    (mappingSelected : Selects environment current (Core.OrderedMapping.encode index.layout entries))
    (keySelected : Selects environment (SourceCoreDataExpressions.projectPacked index.keyPosition prepared.keyTypes keys) key)
    (replacementSelected : Selects environment replacementExpression replacement) :
    ∃ output finalStore administrative,
      OrderedMapping.ValueRel index.layout (KeyRep certificate signatures identities) valueRel updated output ∧
      Evaluates environment store (update prepared [.index index] index.layout.type current keys replacementExpression)
        (.inRight .word output) finalStore ∧ finalStore = store ++ administrative ∧
      administrative.length = 2 * (checked.catalog.entries.length + 1) := by
  obtain ⟨selected, _, selectedEvaluation⟩ := selectedIndex_found certificate prepared faithful keyRep related found
    environment store current keys mappingSelected keySelected
  obtain ⟨output, represented, evaluated⟩ := update_after_selection certificate prepared faithful keyRep replacementRep related
    inserted environment store _ current keys replacementExpression mappingSelected keySelected replacementSelected selectedEvaluation
  obtain ⟨firstCells, firstStore, firstCount⟩ := selectedStore_extension certificate environment store entries key
  obtain ⟨secondCells, secondStore, secondCount⟩ := DataMappingComparison.helper_store_extension certificate.comparison
    (replacement :: selected :: environment) (selectedStore certificate environment store entries key) _ _ _ _
  refine ⟨output, _, firstCells ++ secondCells, represented, evaluated, ?_, ?_⟩
  · change DataMappingComparison.insertStore _ _ _ _ _ _ _ = _
    rw [show DataMappingComparison.insertStore _ _ _ _ _ _ _ = _ from secondStore, firstStore, List.append_assoc]
  · simp only [List.length_append, firstCount, secondCount]
    omega

theorem update_preserves {checked : SourceCoreDataCatalog.Checked} {sourceValue : TypeSystem.Ty} {index : PreparedIndex}
    (certificate : Index checked sourceValue index) (prepared : Prepared)
    {signatures : ProgramSignatures} {identities : Dynamic.Value → Word → Prop}
    (faithful : IdentityFaithful identities) {valueRel : OrderedMapping.Relation}
    {sourceKey sourceSelected sourceReplacement : Dynamic.Value} {key replacement : Value}
    {sources updated : List (Dynamic.Value × Dynamic.Value)} {entries : Core.OrderedMapping.Entries}
    (keyRep : KeyRep certificate signatures identities sourceKey key) (replacementRep : valueRel sourceReplacement replacement)
    (related : OrderedMapping.EntriesRel (KeyRep certificate signatures identities) valueRel sources entries)
    (read : Reads sourceKey sources sourceValue sourceSelected)
    (inserted : Dynamic.MappingInsert sourceKey sourceReplacement sources updated)
    (environment : Environment) (store : Store) (current keys replacementExpression : Expr)
    (mappingSelected : Selects environment current (Core.OrderedMapping.encode index.layout entries))
    (keySelected : Selects environment (SourceCoreDataExpressions.projectPacked index.keyPosition prepared.keyTypes keys) key)
    (replacementSelected : Selects environment replacementExpression replacement) :
    ∃ output finalStore administrative,
      OrderedMapping.ValueRel index.layout (KeyRep certificate signatures identities) valueRel updated output ∧
      Evaluates environment store (update prepared [.index index] index.layout.type current keys replacementExpression)
        (.inRight .word output) finalStore ∧ finalStore = store ++ administrative ∧
      administrative.length = 2 * (checked.catalog.entries.length + 1) := by
  obtain ⟨selected, _, selectedEvaluation⟩ := selectedIndex_preserves certificate prepared faithful keyRep related read
    environment store current keys mappingSelected keySelected
  obtain ⟨output, represented, evaluated⟩ := update_after_selection certificate prepared faithful keyRep replacementRep related
    inserted environment store _ current keys replacementExpression mappingSelected keySelected replacementSelected selectedEvaluation
  obtain ⟨firstCells, firstStore, firstCount⟩ := selectedStore_extension certificate environment store entries key
  obtain ⟨secondCells, secondStore, secondCount⟩ := DataMappingComparison.helper_store_extension certificate.comparison
    (replacement :: selected :: environment) (selectedStore certificate environment store entries key) _ _ _ _
  refine ⟨output, _, firstCells ++ secondCells, represented, evaluated, ?_, ?_⟩
  · change DataMappingComparison.insertStore _ _ _ _ _ _ _ = _
    rw [show DataMappingComparison.insertStore _ _ _ _ _ _ _ = _ from secondStore, firstStore, List.append_assoc]
  · simp only [List.length_append, firstCount, secondCount]
    omega

end Solcore.SourceSemantics.CoreLowering.DataPlaceMappingPath
