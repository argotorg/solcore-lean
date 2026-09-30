import Solcore.Core.OrderedMapping
import Solcore.SourceSemantics.Dynamic.Primitive

/-! Generic library correspondence to independent source ordered mappings.
Key/value representation and the generated comparator's correctness are explicit
boundaries; this is not a certificate for a complete source compiler. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.OrderedMapping

open Core.OrderedMapping

abbrev Relation := Dynamic.Value → Core.Value → Prop

inductive EntriesRel (keyRel valueRel : Relation) :
    List (Dynamic.Value × Dynamic.Value) → Entries → Prop where
  | nil : EntriesRel keyRel valueRel [] []
  | cons {sourceKey sourceValue : Dynamic.Value} {key value : Core.Value}
      {sourceRest : List (Dynamic.Value × Dynamic.Value)} {rest : Entries}
      (keyRelated : keyRel sourceKey key) (valueRelated : valueRel sourceValue value)
      (tail : EntriesRel keyRel valueRel sourceRest rest) :
      EntriesRel keyRel valueRel ((sourceKey, sourceValue) :: sourceRest) ((key, value) :: rest)

def ValueRel (layout : Layout) (keyRel valueRel : Relation)
    (entries : List (Dynamic.Value × Dynamic.Value)) (carrier : Core.Value) : Prop :=
  ∃ coreEntries, EntriesRel keyRel valueRel entries coreEntries ∧ carrier = encode layout coreEntries

/-- Equality may be non-reflexive, for example for ordinary source closures.
No generic equality of functions or mappings is assumed. -/
structure KeyEqualityCorrect (keyRel : Relation) (equal : Predicate) : Prop where
  equivalent : ∀ {sourceKey sourceStored : Dynamic.Value} {key stored : Core.Value},
    keyRel sourceKey key → keyRel sourceStored stored →
      (equal key stored = true ↔ Dynamic.ValueEquivalent sourceKey sourceStored)

theorem EntriesRel.append {keyRel valueRel : Relation}
    {sourceLeft sourceRight : List (Dynamic.Value × Dynamic.Value)} {left right : Entries}
    (leftRelated : EntriesRel keyRel valueRel sourceLeft left)
    (rightRelated : EntriesRel keyRel valueRel sourceRight right) :
    EntriesRel keyRel valueRel (sourceLeft ++ sourceRight) (left ++ right) := by
  induction leftRelated with
  | nil => exact rightRelated
  | cons key value _ ih => exact .cons key value ih

theorem lookup_related {keyRel valueRel : Relation} {equal : Predicate}
    (correct : KeyEqualityCorrect keyRel equal)
    {sourceKey sourceResult : Dynamic.Value} {key : Core.Value}
    {sourceEntries : List (Dynamic.Value × Dynamic.Value)} {entries : Entries}
    (keyRelated : keyRel sourceKey key) (related : EntriesRel keyRel valueRel sourceEntries entries)
    (found : Dynamic.MappingLookup sourceKey sourceEntries sourceResult) :
    ∃ value, lookupEntries equal key entries = some value ∧ valueRel sourceResult value := by
  induction related with
  | nil => cases found
  | @cons sourceStored sourceValue stored value sourceRest rest storedRelated valueRelated tail ih =>
      cases found with
      | head equivalent =>
          have same := (correct.equivalent keyRelated storedRelated).mpr equivalent
          exact ⟨value, by simp [lookupEntries, same], valueRelated⟩
      | tail different found =>
          have unequal : equal key stored = false := Bool.eq_false_iff.mpr
            (fun same => different ((correct.equivalent keyRelated storedRelated).mp same))
          obtain ⟨result, lookup, relation⟩ := ih found
          exact ⟨result, by simpa [lookupEntries, unequal] using lookup, relation⟩

theorem absent_related {keyRel valueRel : Relation} {equal : Predicate}
    (correct : KeyEqualityCorrect keyRel equal)
    {sourceKey : Dynamic.Value} {key : Core.Value}
    {sourceEntries : List (Dynamic.Value × Dynamic.Value)} {entries : Entries}
    (keyRelated : keyRel sourceKey key) (related : EntriesRel keyRel valueRel sourceEntries entries)
    (absent : Dynamic.MappingAbsent sourceKey sourceEntries) :
    lookupEntries equal key entries = none := by
  induction related with
  | nil => rfl
  | @cons sourceStored sourceValue stored value sourceRest rest storedRelated valueRelated tail ih =>
      cases absent with
      | cons different absent =>
          have unequal : equal key stored = false := Bool.eq_false_iff.mpr
            (fun same => different ((correct.equivalent keyRelated storedRelated).mp same))
          simpa [lookupEntries, unequal] using ih absent

private theorem update_related {keyRel valueRel : Relation} {equal : Predicate}
    (correct : KeyEqualityCorrect keyRel equal)
    {sourceKey sourceValue : Dynamic.Value} {key value : Core.Value}
    {sourceEntries updated : List (Dynamic.Value × Dynamic.Value)} {entries : Entries}
    (keyRelated : keyRel sourceKey key) (valueRelated : valueRel sourceValue value)
    (related : EntriesRel keyRel valueRel sourceEntries entries)
    (updatedSource : Dynamic.MappingUpdate sourceKey sourceValue sourceEntries updated) :
    EntriesRel keyRel valueRel updated (insertEntries equal key value entries) := by
  induction related generalizing updated with
  | nil => cases updatedSource
  | @cons sourceStored sourceOld stored old sourceRest rest storedRelated oldRelated tail ih =>
      cases updatedSource with
      | head equivalent =>
          have same := (correct.equivalent keyRelated storedRelated).mpr equivalent
          simp only [insertEntries, same, ↓reduceIte]
          exact .cons keyRelated valueRelated tail
      | tail different updatedSource =>
          have unequal : equal key stored = false := Bool.eq_false_iff.mpr
            (fun same => different ((correct.equivalent keyRelated storedRelated).mp same))
          simp only [insertEntries, unequal, Bool.false_eq_true, ↓reduceIte]
          exact .cons storedRelated oldRelated (ih updatedSource)

private theorem insert_absent {keyRel valueRel : Relation} {equal : Predicate}
    (correct : KeyEqualityCorrect keyRel equal)
    {sourceKey : Dynamic.Value} {key value : Core.Value}
    {sourceEntries : List (Dynamic.Value × Dynamic.Value)} {entries : Entries}
    (keyRelated : keyRel sourceKey key) (related : EntriesRel keyRel valueRel sourceEntries entries)
    (absent : Dynamic.MappingAbsent sourceKey sourceEntries) :
    insertEntries equal key value entries = entries ++ [(key, value)] := by
  induction related with
  | nil => rfl
  | @cons sourceStored sourceOld stored old sourceRest rest storedRelated oldRelated tail ih =>
      cases absent with
      | cons different absent =>
          have unequal : equal key stored = false := Bool.eq_false_iff.mpr
            (fun same => different ((correct.equivalent keyRelated storedRelated).mp same))
          simp [insertEntries, unequal, ih absent]

theorem insert_related {keyRel valueRel : Relation} {equal : Predicate}
    (correct : KeyEqualityCorrect keyRel equal)
    {sourceKey sourceValue : Dynamic.Value} {key value : Core.Value}
    {sourceEntries updated : List (Dynamic.Value × Dynamic.Value)} {entries : Entries}
    (keyRelated : keyRel sourceKey key) (valueRelated : valueRel sourceValue value)
    (related : EntriesRel keyRel valueRel sourceEntries entries)
    (inserted : Dynamic.MappingInsert sourceKey sourceValue sourceEntries updated) :
    EntriesRel keyRel valueRel updated (insertEntries equal key value entries) := by
  cases inserted with
  | update replacement => exact update_related correct keyRelated valueRelated related replacement
  | append absent =>
      rw [insert_absent correct keyRelated related absent]
      exact related.append (.cons keyRelated valueRelated .nil)

/-- A related source insertion and actual pure comparator executions entail a
finite Core run with a related carrier. Administrative cells remain explicit. -/
theorem insert_run_preserves {keyRel valueRel : Relation} {equal : Predicate}
    (correct : KeyEqualityCorrect keyRel equal) (layout : Layout)
    {sourceKey sourceValue : Dynamic.Value} {key value comparator : Core.Value}
    {sourceEntries updated : List (Dynamic.Value × Dynamic.Value)} {entries : Entries}
    (keyRelated : keyRel sourceKey key) (valueRelated : valueRel sourceValue value)
    (related : EntriesRel keyRel valueRel sourceEntries entries)
    (inserted : Dynamic.MappingInsert sourceKey sourceValue sourceEntries updated)
    {environment : Core.Environment} {initialStore mappingStore keyStore valueStore comparisonStore : Core.Store}
    {mapping keyExpr valueExpr keyEqual : Core.Expr}
    (mappingEvaluated : Core.Evaluates environment initialStore mapping (encode layout entries) mappingStore)
    (keyEvaluated : Core.Evaluates environment mappingStore keyExpr key keyStore)
    (valueEvaluated : Core.Evaluates environment keyStore valueExpr value valueStore)
    (comparatorEvaluated : Core.Evaluates environment valueStore keyEqual comparator comparisonStore)
    (comparisons : Comparisons layout comparator equal key entries
      (installedStore comparisonStore layout.insertParameter layout.type (insertBody layout)
        (.pair (encode layout entries) (.pair (.pair key value) comparator)) environment)) :
    ∃ output finalStore required, ValueRel layout keyRel valueRel updated output ∧
      ∀ fuel, required ≤ fuel →
        Core.runStateful fuel (Core.State.initial (insert layout keyEqual mapping keyExpr valueExpr) environment initialStore) =
          .done (.inRight .word output) finalStore := by
  have evaluation := insert_evaluates entries key value comparator equal
    mappingEvaluated keyEvaluated valueEvaluated comparatorEvaluated comparisons
  obtain ⟨required, complete⟩ := Core.evaluation_runStateful_complete_with_sufficient_fuel evaluation
  exact ⟨_, _, required, ⟨_, insert_related correct keyRelated valueRelated related inserted, rfl⟩, complete⟩

theorem lookup_found_run_preserves {keyRel valueRel : Relation} {equal : Predicate}
    (correct : KeyEqualityCorrect keyRel equal) (layout : Layout)
    {sourceKey sourceResult : Dynamic.Value} {key comparator : Core.Value}
    {sourceEntries : List (Dynamic.Value × Dynamic.Value)} {entries : Entries}
    (keyRelated : keyRel sourceKey key) (related : EntriesRel keyRel valueRel sourceEntries entries)
    (found : Dynamic.MappingLookup sourceKey sourceEntries sourceResult)
    {environment : Core.Environment} {initialStore mappingStore keyStore comparisonStore : Core.Store}
    {mapping keyExpr keyEqual : Core.Expr}
    (mappingEvaluated : Core.Evaluates environment initialStore mapping (encode layout entries) mappingStore)
    (keyEvaluated : Core.Evaluates environment mappingStore keyExpr key keyStore)
    (comparatorEvaluated : Core.Evaluates environment keyStore keyEqual comparator comparisonStore)
    (comparisons : Comparisons layout comparator equal key entries
      (installedStore comparisonStore layout.lookupParameter layout.lookupResult (lookupBody layout)
        (.pair (encode layout entries) (.pair key comparator)) environment)) :
    ∃ output finalStore required, valueRel sourceResult output ∧
      ∀ fuel, required ≤ fuel →
        Core.runStateful fuel (Core.State.initial (lookup layout keyEqual mapping keyExpr) environment initialStore) =
          .done (.inRight .word (.inRight .unit output)) finalStore := by
  obtain ⟨output, located, represented⟩ := lookup_related correct keyRelated related found
  have evaluation := lookup_evaluates entries key comparator equal
    mappingEvaluated keyEvaluated comparatorEvaluated comparisons
  rw [located] at evaluation
  obtain ⟨required, complete⟩ := Core.evaluation_runStateful_complete_with_sufficient_fuel evaluation
  exact ⟨output, _, required, represented, complete⟩

theorem lookup_absent_run_preserves {keyRel valueRel : Relation} {equal : Predicate}
    (correct : KeyEqualityCorrect keyRel equal) (layout : Layout)
    {sourceKey : Dynamic.Value} {key comparator : Core.Value}
    {sourceEntries : List (Dynamic.Value × Dynamic.Value)} {entries : Entries}
    (keyRelated : keyRel sourceKey key) (related : EntriesRel keyRel valueRel sourceEntries entries)
    (absent : Dynamic.MappingAbsent sourceKey sourceEntries)
    {environment : Core.Environment} {initialStore mappingStore keyStore comparisonStore : Core.Store}
    {mapping keyExpr keyEqual : Core.Expr}
    (mappingEvaluated : Core.Evaluates environment initialStore mapping (encode layout entries) mappingStore)
    (keyEvaluated : Core.Evaluates environment mappingStore keyExpr key keyStore)
    (comparatorEvaluated : Core.Evaluates environment keyStore keyEqual comparator comparisonStore)
    (comparisons : Comparisons layout comparator equal key entries
      (installedStore comparisonStore layout.lookupParameter layout.lookupResult (lookupBody layout)
        (.pair (encode layout entries) (.pair key comparator)) environment)) :
    ∃ finalStore required, ∀ fuel, required ≤ fuel →
      Core.runStateful fuel (Core.State.initial (lookup layout keyEqual mapping keyExpr) environment initialStore) =
        .done (.inRight .word (.inLeft layout.valueType .unit)) finalStore := by
  have evaluation := lookup_evaluates entries key comparator equal
    mappingEvaluated keyEvaluated comparatorEvaluated comparisons
  rw [absent_related correct keyRelated related absent] at evaluation
  obtain ⟨required, complete⟩ := Core.evaluation_runStateful_complete_with_sufficient_fuel evaluation
  exact ⟨_, required, complete⟩

/-- Source insertion is related to the actual post-RHS root write; earlier root
contents are unrestricted. Comparator setup also precedes the final root read. -/
theorem assign_latest_preserves {keyRel valueRel : Relation} {equal : Predicate}
    (correct : KeyEqualityCorrect keyRel equal) (layout : Layout)
    {sourceKey sourceValue : Dynamic.Value} {key value comparator : Core.Value}
    {sourceEntries updated : List (Dynamic.Value × Dynamic.Value)} {entries : Entries}
    (keyRelated : keyRel sourceKey key) (valueRelated : valueRel sourceValue value)
    (related : EntriesRel keyRel valueRel sourceEntries entries)
    (inserted : Dynamic.MappingInsert sourceKey sourceValue sourceEntries updated)
    {environment : Core.Environment} {initialStore referenceStore keyStore rhsStore comparisonStore : Core.Store}
    {keyEqual reference keyExpr rhs : Core.Expr} {location : Core.Location}
    (referenceEvaluated : Core.Evaluates environment initialStore reference
      (.cellRef (Core.OptionalCell.cellType layout.type) location) referenceStore)
    (keyEvaluated : Core.Evaluates (.cellRef (Core.OptionalCell.cellType layout.type) location :: environment)
      referenceStore (keyExpr.weakenAt 0) (.inRight .word key) keyStore)
    (rhsEvaluated : Core.Evaluates (key :: .cellRef (Core.OptionalCell.cellType layout.type) location :: environment)
      keyStore ((rhs.weakenAt 0).weakenAt 0) (.inRight .word value) rhsStore)
    (comparisonEvaluated : Core.Evaluates
      (value :: key :: .cellRef (Core.OptionalCell.cellType layout.type) location :: environment)
      rhsStore (((keyEqual.weakenAt 0).weakenAt 0).weakenAt 0) comparator comparisonStore)
    (latest : comparisonStore.read? location = some (.inRight .unit (encode layout entries)))
    (comparisons : Comparisons layout comparator equal key entries
      (assignInsertStore layout comparisonStore entries key value comparator location environment)) :
    ∃ output finalStore, ValueRel layout keyRel valueRel updated output ∧
      finalStore.read? location = some (.inRight .unit output) ∧
      Core.Evaluates environment initialStore (assign layout keyEqual reference keyExpr rhs)
        (.inRight .word .unit) finalStore := by
  refine ⟨_, _, ⟨_, insert_related correct keyRelated valueRelated related inserted, rfl⟩, ?_,
    assign_latest_evaluates entries key value comparator equal
      referenceEvaluated keyEvaluated rhsEvaluated comparisonEvaluated latest comparisons⟩
  have inBounds : location < comparisonStore.length := (List.getElem?_eq_some_iff.mp latest).choose
  have allocatedBounds : location <
      (assignInsertStore layout comparisonStore entries key value comparator location environment).length := by
    simpa [assignInsertStore, installedStore, Core.WordMapping.installedStore] using Nat.lt_succ_of_lt inBounds
  simp [Core.Store.read?, allocatedBounds]

end Solcore.SourceSemantics.CoreLowering.OrderedMapping
