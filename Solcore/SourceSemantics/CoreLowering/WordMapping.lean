import Solcore.Core.WordMapping
import Solcore.SourceSemantics.Dynamic.Primitive

/-! Structural correspondence for the fixed Word/Word mapping prototype.
The source side is the independent declarative ordered-mapping semantics.
There is no call to the executable typed-source runtime. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.WordMapping

open Core

def sourceEntries : Core.WordMapping.Entries → List (Dynamic.Value × Dynamic.Value)
  | [] => []
  | (key, value) :: rest => (.word key, .word value) :: sourceEntries rest

/-- Ordered entries are represented structurally, including duplicate keys. -/
inductive ValueRel : List (Dynamic.Value × Dynamic.Value) → Core.Value → Prop where
  | nil : ValueRel [] (.constructed Core.WordMapping.nilConstructor .unit)
  | cons {entries : List (Dynamic.Value × Dynamic.Value)} {tail : Core.Value}
      (key value : Word) (rest : ValueRel entries tail) :
      ValueRel ((.word key, .word value) :: entries)
        (.constructed Core.WordMapping.consConstructor (.pair (.pair (.word key) (.word value)) tail))

/-- The whole source value retains its declared key and value types. -/
def MappingValueRel (source : Dynamic.Value) (target : Core.Value) : Prop :=
  ∃ entries, source = .mapping .word .word entries ∧ ValueRel entries target

theorem ValueRel.encode (entries : Core.WordMapping.Entries) :
    ValueRel (sourceEntries entries) (Core.WordMapping.encode entries) := by
  induction entries with
  | nil => exact .nil
  | cons entry rest ih => exact .cons entry.1 entry.2 ih

theorem ValueRel.canonical {entries : List (Dynamic.Value × Dynamic.Value)} {value : Core.Value}
    (related : ValueRel entries value) :
    ∃ words : Core.WordMapping.Entries, entries = sourceEntries words ∧ value = Core.WordMapping.encode words := by
  induction related with
  | nil => exact ⟨[], rfl, rfl⟩
  | cons key value rest ih =>
      obtain ⟨words, rfl, rfl⟩ := ih
      exact ⟨(key, value) :: words, rfl, rfl⟩

theorem ValueRel.hasType {entries : List (Dynamic.Value × Dynamic.Value)} {value : Core.Value}
    (related : ValueRel entries value) (world : StoreTyping) :
    RuntimeValueHasType world value Core.WordMapping.type Core.WordMapping.actualDefinitions := by
  obtain ⟨words, _, rfl⟩ := related.canonical
  exact Core.WordMapping.encode_hasType words world

private theorem word_equivalent (left right : Word) :
    Dynamic.ValueEquivalent (.word left) (.word right) ↔ left = right := by
  constructor
  · intro same
    exact Dynamic.Value.word.inj same.1
  · rintro rfl
    exact ⟨rfl, .word _⟩

theorem lookupEntries_of_lookup (words : Core.WordMapping.Entries) (key : Word)
    {result : Dynamic.Value}
    (lookup : Dynamic.MappingLookup (.word key) (sourceEntries words) result) :
    result = .word (Core.WordMapping.lookupEntries key words) := by
  induction words with
  | nil => cases lookup
  | cons entry rest ih =>
      rcases entry with ⟨storedKey, value⟩
      cases lookup with
      | head equivalent =>
          have same := (word_equivalent key storedKey).mp equivalent
          simp [Core.WordMapping.lookupEntries, same]
      | tail different lookup =>
          have distinct : key ≠ storedKey := fun same => different ((word_equivalent _ _).mpr same)
          simpa [Core.WordMapping.lookupEntries, distinct] using ih lookup

theorem lookupEntries_of_absent (words : Core.WordMapping.Entries) (key : Word)
    (absent : Dynamic.MappingAbsent (.word key) (sourceEntries words)) :
    Core.WordMapping.lookupEntries key words = Word.zero := by
  induction words with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨storedKey, value⟩
      cases absent with
      | cons different absent =>
          have distinct : key ≠ storedKey := fun same => different ((word_equivalent _ _).mpr same)
          simpa [Core.WordMapping.lookupEntries, distinct] using ih absent

private theorem insert_tail {key value storedKey storedValue : Dynamic.Value}
    {entries updated : List (Dynamic.Value × Dynamic.Value)}
    (different : ¬ Dynamic.ValueEquivalent key storedKey)
    (inserted : Dynamic.MappingInsert key value entries updated) :
    Dynamic.MappingInsert key value ((storedKey, storedValue) :: entries)
      ((storedKey, storedValue) :: updated) := by
  cases inserted with
  | update replacement => exact .update (.tail different replacement)
  | append absent => exact .append (.cons different absent)

/-- The Core specification is accepted by the independent first-update or
append-at-end source relation. No uniqueness assumption on keys is needed. -/
theorem insertEntries_source (words : Core.WordMapping.Entries) (key value : Word) :
    Dynamic.MappingInsert (.word key) (.word value) (sourceEntries words)
      (sourceEntries (Core.WordMapping.insertEntries key value words)) := by
  induction words with
  | nil => exact .append .nil
  | cons entry rest ih =>
      rcases entry with ⟨storedKey, storedValue⟩
      by_cases same : key = storedKey
      · simpa [Core.WordMapping.insertEntries, same, sourceEntries] using
          (Dynamic.MappingInsert.update
            (Dynamic.MappingUpdate.head (entries := sourceEntries rest)
              (storedValue := Dynamic.Value.word storedValue)
              ((word_equivalent key storedKey).mpr same)))
      · have different : ¬ Dynamic.ValueEquivalent (.word key) (.word storedKey) :=
          fun equivalent => same ((word_equivalent _ _).mp equivalent)
        simp only [Core.WordMapping.insertEntries, beq_eq_false_iff_ne.mpr same, Bool.false_eq_true,
          ↓reduceIte, sourceEntries]
        exact insert_tail different ih

/-- Any source insertion has exactly the ordered carrier computed by Core. -/
theorem insertEntries_of_insert (words : Core.WordMapping.Entries) (key value : Word)
    {updated : List (Dynamic.Value × Dynamic.Value)}
    (inserted : Dynamic.MappingInsert (.word key) (.word value) (sourceEntries words) updated) :
    updated = sourceEntries (Core.WordMapping.insertEntries key value words) :=
  Dynamic.MappingInsert.functional inserted (insertEntries_source words key value)

theorem lookup_present_preserves
    {environment : Core.Environment} {initialStore mappingStore keyStore : Core.Store}
    {mapping keyExpr : Core.Expr} {entries : List (Dynamic.Value × Dynamic.Value)}
    {carrier : Core.Value} {key result : Word}
    (related : ValueRel entries carrier)
    (lookup : Dynamic.MappingLookup (.word key) entries (.word result))
    (mappingEvaluated : Evaluates environment initialStore mapping carrier mappingStore)
    (keyEvaluated : Evaluates environment mappingStore keyExpr (.word key) keyStore) :
    ∃ finalStore,
      Evaluates environment initialStore (Core.WordMapping.lookup mapping keyExpr)
        (.inRight .word (.word result)) finalStore := by
  obtain ⟨words, rfl, rfl⟩ := related.canonical
  have same : result = Core.WordMapping.lookupEntries key words :=
    Dynamic.Value.word.inj (lookupEntries_of_lookup words key lookup)
  subst result
  exact ⟨_, Core.WordMapping.lookup_evaluates words key mappingEvaluated keyEvaluated⟩

theorem lookup_absent_preserves
    {environment : Core.Environment} {initialStore mappingStore keyStore : Core.Store}
    {mapping keyExpr : Core.Expr} {entries : List (Dynamic.Value × Dynamic.Value)}
    {carrier : Core.Value} {key : Word}
    (related : ValueRel entries carrier)
    (absent : Dynamic.MappingAbsent (.word key) entries)
    (mappingEvaluated : Evaluates environment initialStore mapping carrier mappingStore)
    (keyEvaluated : Evaluates environment mappingStore keyExpr (.word key) keyStore) :
    ∃ finalStore,
      Evaluates environment initialStore (Core.WordMapping.lookup mapping keyExpr)
        (.inRight .word (.word Word.zero)) finalStore := by
  obtain ⟨words, rfl, rfl⟩ := related.canonical
  obtain evaluated := Core.WordMapping.lookup_evaluates words key mappingEvaluated keyEvaluated
  rw [lookupEntries_of_absent words key absent] at evaluated
  exact ⟨_, evaluated⟩

theorem insert_preserves
    {environment : Core.Environment} {initialStore mappingStore keyStore valueStore : Core.Store}
    {mapping keyExpr valueExpr : Core.Expr}
    {entries updated : List (Dynamic.Value × Dynamic.Value)}
    {carrier : Core.Value} {key value : Word}
    (related : ValueRel entries carrier)
    (inserted : Dynamic.MappingInsert (.word key) (.word value) entries updated)
    (mappingEvaluated : Evaluates environment initialStore mapping carrier mappingStore)
    (keyEvaluated : Evaluates environment mappingStore keyExpr (.word key) keyStore)
    (valueEvaluated : Evaluates environment keyStore valueExpr (.word value) valueStore) :
    ∃ output finalStore, ValueRel updated output ∧
      Evaluates environment initialStore (Core.WordMapping.insert mapping keyExpr valueExpr)
        (.inRight .word output) finalStore := by
  obtain ⟨words, rfl, rfl⟩ := related.canonical
  rw [insertEntries_of_insert words key value inserted]
  exact ⟨_, _, ValueRel.encode _, Core.WordMapping.insert_evaluates words key value
    mappingEvaluated keyEvaluated valueEvaluated⟩

/-- Independent source insertion entails a finite Core runner observation. -/
theorem insert_run_preserves
    {environment : Core.Environment} {initialStore mappingStore keyStore valueStore : Core.Store}
    {mapping keyExpr valueExpr : Core.Expr}
    {entries updated : List (Dynamic.Value × Dynamic.Value)}
    {carrier : Core.Value} {key value : Word}
    (related : ValueRel entries carrier)
    (inserted : Dynamic.MappingInsert (.word key) (.word value) entries updated)
    (mappingEvaluated : Evaluates environment initialStore mapping carrier mappingStore)
    (keyEvaluated : Evaluates environment mappingStore keyExpr (.word key) keyStore)
    (valueEvaluated : Evaluates environment keyStore valueExpr (.word value) valueStore) :
    ∃ output finalStore required, ValueRel updated output ∧
      ∀ fuel, required ≤ fuel →
        runStateful fuel (State.initial (Core.WordMapping.insert mapping keyExpr valueExpr) environment initialStore) =
          .done (.inRight .word output) finalStore := by
  obtain ⟨output, finalStore, related, evaluated⟩ := insert_preserves related inserted
    mappingEvaluated keyEvaluated valueEvaluated
  obtain ⟨required, complete⟩ := evaluation_runStateful_complete_with_sufficient_fuel evaluated
  exact ⟨output, finalStore, required, related, complete⟩

/-- A source update of the root *after RHS effects* is preserved by the actual
Core writeback helper, and its resulting root contains the related carrier. -/
theorem assign_latest_preserves
    {environment : Core.Environment}
    {initialStore referenceStore keyStore rhsStore : Core.Store}
    {reference keyExpr rhs : Core.Expr} {location : Core.Location}
    {entries updated : List (Dynamic.Value × Dynamic.Value)}
    {carrier : Core.Value} {key value : Word}
    (related : ValueRel entries carrier)
    (inserted : Dynamic.MappingInsert (.word key) (.word value) entries updated)
    (referenceEvaluated : Evaluates environment initialStore reference
      (.cellRef (OptionalCell.cellType Core.WordMapping.type) location) referenceStore)
    (keyEvaluated : Evaluates
      (.cellRef (OptionalCell.cellType Core.WordMapping.type) location :: environment)
      referenceStore (keyExpr.weakenAt 0) (.inRight .word (.word key)) keyStore)
    (rhsEvaluated : Evaluates
      (.word key :: .cellRef (OptionalCell.cellType Core.WordMapping.type) location :: environment)
      keyStore ((rhs.weakenAt 0).weakenAt 0) (.inRight .word (.word value)) rhsStore)
    (latest : rhsStore.read? location = some (.inRight .unit carrier)) :
    ∃ output finalStore, ValueRel updated output ∧
      finalStore.read? location = some (.inRight .unit output) ∧
      Evaluates environment initialStore (Core.WordMapping.assign reference keyExpr rhs)
        (.inRight .word .unit) finalStore := by
  obtain ⟨words, rfl, rfl⟩ := related.canonical
  rw [insertEntries_of_insert words key value inserted]
  refine ⟨_, _, ValueRel.encode _, ?_,
    Core.WordMapping.assign_latest_evaluates words key value
      referenceEvaluated keyEvaluated rhsEvaluated latest⟩
  have inBounds : location < rhsStore.length := (List.getElem?_eq_some_iff.mp latest).choose
  have installedBounds : location <
      (Core.WordMapping.assignInsertStore rhsStore words key value location environment).length := by
    simpa [Core.WordMapping.assignInsertStore, Core.WordMapping.installedStore] using
      Nat.lt_succ_of_lt inBounds
  simp [Store.read?, installedBounds]

end Solcore.SourceSemantics.CoreLowering.WordMapping
