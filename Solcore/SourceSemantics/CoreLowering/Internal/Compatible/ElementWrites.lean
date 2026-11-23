import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.ArrayEvaluation
import Solcore.SourceSemantics.CoreLowering.Internal.Data.PlaceMappings
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.PlaceWriteback

/-!
# Writes to an element of a local memory array

The code `SourceCoreCompatibleDataPlaces.lowerElements` emits for `a[i] = v`, `a[i] op= v` or `a[i] ~=` on a
local array `a`: the root's load, then `arrayElementWrite` at one element. Its runs are compositions of the
Core rules, as `DataPlaceExecution`'s are for a route's `execute`: the root not yet initialized, the index's
failure, `0x32` from the array's length on, the right side's or `modified`'s failure, and the write and the
continuation, plain or compound. The receipt inverts the compiler at one element, and a renaming renames the
root's slot and the children. Main declarations: `CompatibleElementWrites.code`, `plain_evaluates`,
`compound_evaluates`, `generated_of_lower` and `code_rename`.
-/

set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleElementWrites
open Core Frontend SourceCoreCompatibleDataPlaces

/-- The code `lowerElements` emits for a write to one element of the local whose cell `slot` names. -/
def code (slot : Nat) (storedType outputType : Ty) (invalid : Word) (comparison value next : Expr)
    (modifier : Option ElementModifier) (layout : OrderedMapping.Layout) (index : Expr) : Expr :=
  LanguageResult.bind outputType
    (.caseE (.loadCell (.var slot)) (LanguageResult.failure storedType (.word invalid))
      (LanguageResult.success (.var 0)))
    (arrayElementWrite outputType comparison value next modifier 1 [(layout, index)])

theorem shift_closed {checked : SourceCoreCompatibleCatalog.Checked}
    (comparison : SourceCoreCompatibleDataEquality.Prepared checked) :
    ∀ count, shift count comparison.expression = comparison.expression
  | 0 => rfl
  | count + 1 => by
    rw [shift, List.range_succ, List.foldl_append, ← shift, shift_closed comparison count]
    exact CompatibleMapping.Transport.expression_weaken comparison

private theorem write_at {store : Store} {location : Location} (bound : location < store.length) (value : Value) :
    store.write? location value = some (store.set location value) := by
  simp [Store.write?, bound]

section
variable {environment : Environment} {store : Store} {slot : Nat} {storedType outputType cellType : Ty}
  {invalid : Word} {comparison value next : Expr} {modifier : Option ElementModifier}
  {layout : OrderedMapping.Layout} {index : Expr} {location : Location}

/-- A root not yet initialized: its cell holds the left of its option, and the write fails with the
site's reason before its index. -/
theorem root_empty {payloadType : Ty} {payload : Value}
    (reference : environment[slot]? = some (.cellRef cellType location))
    (empty : store.read? location = some (.inLeft payloadType payload)) :
    Evaluates environment store (code slot storedType outputType invalid comparison value next modifier layout index)
      (.inLeft outputType (.word invalid)) store :=
  LanguageResult.bind_failure _ (.caseLeft (.loadCell (.var reference) empty) (.inLeft .word))

/-- The root's array: the right of its option. -/
theorem root_full {leftType : Ty} {array : Value}
    (reference : environment[slot]? = some (.cellRef cellType location))
    (full : store.read? location = some (.inRight leftType array)) :
    Evaluates environment store
      (.caseE (.loadCell (.var slot)) (LanguageResult.failure storedType (.word invalid))
        (LanguageResult.success (.var 0)))
      (.inRight .word array) store :=
  .caseRight (.loadCell (.var reference) full) (.inRight (.var rfl))

theorem index_failure {leftType indexType : Ty} {array : Value} {reason : Word} {after : Store}
    (reference : environment[slot]? = some (.cellRef cellType location))
    (full : store.read? location = some (.inRight leftType array))
    (failed : Evaluates (array :: environment) store (shift 1 index) (.inLeft indexType (.word reason)) after) :
    Evaluates environment store (code slot storedType outputType invalid comparison value next modifier layout index)
      (.inLeft outputType (.word reason)) after := by
  apply LanguageResult.bind_success _ (root_full reference full)
  simp only [arrayElementWrite]
  exact LanguageResult.bind_failure _ failed

theorem outOfBounds {leftType elementType : Ty} {arrayLocation : Location} {position length : Word} {rest : Value}
    {after : Store}
    (reference : environment[slot]? = some (.cellRef cellType location))
    (full : store.read? location = some (.inRight leftType (.cellRef elementType arrayLocation)))
    (indexed : Evaluates (.cellRef elementType arrayLocation :: environment) store (shift 1 index)
      (.inRight .word (.word position)) after)
    (read : after.read? arrayLocation = some (.pair (.word length) rest)) (beyond : ¬ position < length) :
    Evaluates environment store (code slot storedType outputType invalid comparison value next modifier layout index)
      (.inLeft outputType (.word (SourceCorePanics.reason SourceCorePanics.outOfBounds))) after := by
  apply LanguageResult.bind_success _ (root_full reference full)
  simp only [arrayElementWrite]
  apply LanguageResult.bind_success _ indexed
  apply Evaluates.ifFalse
  · simpa only [beyond, decide_false] using
      CompatibleArrayEvaluation.wordLt_evaluates
        (environment := .word position :: .cellRef elementType arrayLocation :: environment) (store := after)
        (left := .var 0) (right := .first (.loadCell (.var 1))) (weakened := .first (.loadCell (.var 2)))
        (by simp [Expr.weakenAt]) (.var rfl) (.first (.loadCell (.var rfl) read))
  · exact .inLeft .word

/-- The bound's check passes below the array's length. -/
theorem within_check {elementType : Ty} {arrayLocation : Location} {position length : Word} {rest : Value}
    {after : Store} (read : after.read? arrayLocation = some (.pair (.word length) rest)) (within : position < length) :
    Evaluates (.word position :: .cellRef elementType arrayLocation :: environment) after
      (Core.Expr.wordLt (.var 0) (.first (.loadCell (.var 1)))) (.bool true) after := by
  simpa only [within, decide_true] using
    CompatibleArrayEvaluation.wordLt_evaluates
      (environment := .word position :: .cellRef elementType arrayLocation :: environment) (store := after)
      (left := .var 0) (right := .first (.loadCell (.var 1))) (weakened := .first (.loadCell (.var 2)))
      (by simp [Expr.weakenAt]) (.var rfl) (.first (.loadCell (.var rfl) read))

theorem plain_rhs_failure {leftType elementType rightType : Ty} {arrayLocation : Location} {position length : Word}
    {rest : Value} {reason : Word} {after final : Store}
    (reference : environment[slot]? = some (.cellRef cellType location))
    (full : store.read? location = some (.inRight leftType (.cellRef elementType arrayLocation)))
    (indexed : Evaluates (.cellRef elementType arrayLocation :: environment) store (shift 1 index)
      (.inRight .word (.word position)) after)
    (read : after.read? arrayLocation = some (.pair (.word length) rest)) (within : position < length)
    (failed : Evaluates (.word position :: .cellRef elementType arrayLocation :: environment) after (shift 2 value)
      (.inLeft rightType (.word reason)) final) :
    Evaluates environment store (code slot storedType outputType invalid comparison value next none layout index)
      (.inLeft outputType (.word reason)) final := by
  apply LanguageResult.bind_success _ (root_full reference full)
  simp only [arrayElementWrite]
  apply LanguageResult.bind_success _ indexed
  apply Evaluates.ifTrue (within_check read within)
  simp only [elementStore]
  exact LanguageResult.bind_failure _ failed

end

/-- A plain write below the array's length: the right side's run, then the array's cell takes its value at
the index, keeping its length and default element, and `next` runs with the five binders. -/
theorem plain_evaluates {checked : SourceCoreCompatibleCatalog.Checked} {fuel : Nat}
    {comparison : SourceCoreCompatibleDataEquality.Prepared checked}
    (prepared : SourceCoreCompatibleDataEquality.prepare fuel checked (.constructor (.builtin .word)) = .ok comparison)
    {layout : OrderedMapping.Layout} (keyType : layout.keyType = .word)
    {environment : Environment} {store : Store} {slot : Nat} {storedType outputType cellType : Ty} {invalid : Word}
    {value next index : Expr} {location : Location} {leftType elementType : Ty} {arrayLocation : Location}
    {position length length' : Word} {rest default stored result : Value} {entries : OrderedMapping.Entries}
    {after rhsStore final : Store}
    (reference : environment[slot]? = some (.cellRef cellType location))
    (full : store.read? location = some (.inRight leftType (.cellRef elementType arrayLocation)))
    (indexed : Evaluates (.cellRef elementType arrayLocation :: environment) store (shift 1 index)
      (.inRight .word (.word position)) after)
    (read : after.read? arrayLocation = some (.pair (.word length) rest)) (within : position < length)
    (rhsEvaluated : Evaluates (.word position :: .cellRef elementType arrayLocation :: environment) after
      (shift 2 value) (.inRight .word stored) rhsStore)
    (current : rhsStore.read? arrayLocation =
      some (.pair (.word length') (.pair default (OrderedMapping.encode layout entries))))
    (wordKeys : ∀ key value, (key, value) ∈ entries → ∃ word, key = .word word)
    (nextEvaluated : Evaluates
      (.unit :: OrderedMapping.encode layout
          (OrderedMapping.insertEntries GenericHeap.arrayKeyEqual (.word position) stored entries) ::
        stored :: .word position :: .cellRef elementType arrayLocation :: environment)
      ((CompatibleMappingComparison.insertStore comparison layout
          (stored :: .word position :: .cellRef elementType arrayLocation :: environment) rhsStore entries
          (.word position) stored).set arrayLocation
        (.pair (.word length') (.pair default (OrderedMapping.encode layout
          (OrderedMapping.insertEntries GenericHeap.arrayKeyEqual (.word position) stored entries)))))
      (shift 5 next) result final) :
    Evaluates environment store
      (code slot storedType outputType invalid comparison.expression value next none layout index) result final := by
  apply LanguageResult.bind_success _ (root_full reference full)
  simp only [arrayElementWrite]
  apply LanguageResult.bind_success _ indexed
  apply Evaluates.ifTrue (within_check read within)
  simp only [elementStore]
  apply LanguageResult.bind_success _ rhsEvaluated
  rw [shift_closed comparison]
  let stack := stored :: .word position :: .cellRef elementType arrayLocation :: environment
  have inserted := OrderedMapping.insert_evaluates (environment := stack)
    (mapping := .second (.second (.loadCell (.var 2)))) (keyExpr := .var 1) (valueExpr := .var 0)
    (keyEqual := comparison.expression) entries (.word position) stored
    (CompatibleMappingComparison.comparator comparison stack rhsStore) GenericHeap.arrayKeyEqual
    (.second (.second (.loadCell (.var rfl) current))) (.var rfl) (.var rfl)
    (CompatibleEquality.prepared_evaluates_exact comparison stack rhsStore)
    (CompatibleArrayEvaluation.word_comparisons prepared keyType stack rhsStore wordKeys position _)
  apply LanguageResult.bind_success _ inserted
  have bound : arrayLocation < rhsStore.length := (List.getElem?_eq_some_iff.mp current).1
  have kept : (CompatibleMappingComparison.insertStore comparison layout stack rhsStore entries (.word position)
      stored).read? arrayLocation =
        some (.pair (.word length') (.pair default (OrderedMapping.encode layout entries))) := by
    simp only [CompatibleMappingComparison.insertStore, OrderedMapping.installedStore, WordMapping.installedStore,
      CompatibleMappingComparison.comparisonStore, Store.read?, List.append_assoc] at current ⊢
    rw [List.getElem?_append_left bound]
    exact current
  have keptBound : arrayLocation <
      (CompatibleMappingComparison.insertStore comparison layout stack rhsStore entries (.word position)
        stored).length :=
    (List.getElem?_eq_some_iff.mp kept).1
  exact .letE (.storeCell (.var rfl) kept
    (.pair (.first (.loadCell (.var rfl) kept)) (.pair (.first (.second (.loadCell (.var rfl) kept))) (.var rfl)))
    (write_at keptBound _)) nextEvaluated

/-! ### Compound writes and in-place `~`

The present element or the array's default at the index (`snapshot`), the right side, `modified`'s leaf,
the insert, `guard`'s check and the store, under the eight binders of `elementStore`. -/

section Compound
variable {checked : SourceCoreCompatibleCatalog.Checked}
  {comparison : SourceCoreCompatibleDataEquality.Prepared checked}
  {layout : OrderedMapping.Layout} {environment : Environment} {store : Store} {slot : Nat}
  {storedType outputType cellType : Ty} {invalid : Word} {value next index : Expr} {location : Location}
  {leftType elementType : Ty} {arrayLocation : Location} {position length : Word} {rest : Value}
  {modifier : ElementModifier} {after lookupStore : Store} {found snapshot : Value}

/-- The snapshot of an absent element: the array's default, as a read's. -/
theorem snapshot_absent {absentType : Ty} {payload length' default mapping : Value}
    (read : lookupStore.read? arrayLocation = some (.pair length' (.pair default mapping))) :
    Evaluates (.inLeft absentType payload :: .word position :: .cellRef elementType arrayLocation :: environment)
      lookupStore
      (.caseE (.var 0) (LanguageResult.success (.inRight .unit (.first (.second (.loadCell (.var 3))))))
        (LanguageResult.success (.inRight .unit (.var 0))))
      (.inRight .word (.inRight .unit default)) lookupStore :=
  .caseLeft (.var rfl) (.inRight (.inRight (.first (.second (.loadCell (.var rfl) read)))))

/-- The snapshot of a present element: the element. -/
theorem snapshot_present {presentType : Ty} {element : Value} :
    Evaluates (.inRight presentType element :: .word position :: .cellRef elementType arrayLocation :: environment)
      lookupStore
      (.caseE (.var 0) (LanguageResult.success (.inRight .unit (.first (.second (.loadCell (.var 3))))))
        (LanguageResult.success (.inRight .unit (.var 0))))
      (.inRight .word (.inRight .unit element)) lookupStore :=
  .caseRight (.var rfl) (.inRight (.inRight (.var rfl)))

/-- The prefix of a compound write or a `~`, to its right side: the root, the index under the bound, the
lookup and the snapshot. -/
private theorem compound_prefix {rightResult : Value} {final : Store}
    (reference : environment[slot]? = some (.cellRef cellType location))
    (full : store.read? location = some (.inRight leftType (.cellRef elementType arrayLocation)))
    (indexed : Evaluates (.cellRef elementType arrayLocation :: environment) store (shift 1 index)
      (.inRight .word (.word position)) after)
    (read : after.read? arrayLocation = some (.pair (.word length) rest)) (within : position < length)
    (lookedUp : Evaluates (.word position :: .cellRef elementType arrayLocation :: environment) after
      (OrderedMapping.lookup layout comparison.expression (.second (.second (.loadCell (.var 1)))) (.var 0))
      (.inRight .word found) lookupStore)
    (snapshotted : Evaluates (found :: .word position :: .cellRef elementType arrayLocation :: environment) lookupStore
      (.caseE (.var 0) (LanguageResult.success (.inRight .unit (.first (.second (.loadCell (.var 3))))))
        (LanguageResult.success (.inRight .unit (.var 0))))
      (.inRight .word snapshot) lookupStore)
    (rest' : Evaluates (snapshot :: found :: .word position :: .cellRef elementType arrayLocation :: environment)
      lookupStore
      (LanguageResult.bind outputType (shift (1 + 3) value)
        (LanguageResult.bind outputType
          (modified modifier.leafType modifier.operator modifier.bitNot (.var 1) (.var 0) modifier.invalidOperand
            modifier.wrap)
          (LanguageResult.bind outputType
            (OrderedMapping.insert layout (shift (1 + 5) comparison.expression)
              (.second (.second (.loadCell (.var 5)))) (.var 4) (.var 0))
            (SourceCoreDataPlaces.guard outputType modifier.operator
              (.letE (.storeCell (.var 6) (.pair (.first (.loadCell (.var 6)))
                  (.pair (.first (.second (.loadCell (.var 6)))) (.var 0))))
                (shift (1 + 7) next))))))
      rightResult final) :
    Evaluates environment store
      (code slot storedType outputType invalid comparison.expression value next (some modifier) layout index)
      rightResult final := by
  apply LanguageResult.bind_success _ (root_full reference full)
  simp only [arrayElementWrite]
  apply LanguageResult.bind_success _ indexed
  apply Evaluates.ifTrue (within_check read within)
  simp only [elementStore]
  rw [shift_closed comparison]
  exact LanguageResult.bind_success _ lookedUp (LanguageResult.bind_success _ snapshotted rest')

theorem compound_rhs_failure {rightType : Ty} {reason : Word} {final : Store}
    (reference : environment[slot]? = some (.cellRef cellType location))
    (full : store.read? location = some (.inRight leftType (.cellRef elementType arrayLocation)))
    (indexed : Evaluates (.cellRef elementType arrayLocation :: environment) store (shift 1 index)
      (.inRight .word (.word position)) after)
    (read : after.read? arrayLocation = some (.pair (.word length) rest)) (within : position < length)
    (lookedUp : Evaluates (.word position :: .cellRef elementType arrayLocation :: environment) after
      (OrderedMapping.lookup layout comparison.expression (.second (.second (.loadCell (.var 1)))) (.var 0))
      (.inRight .word found) lookupStore)
    (snapshotted : Evaluates (found :: .word position :: .cellRef elementType arrayLocation :: environment) lookupStore
      (.caseE (.var 0) (LanguageResult.success (.inRight .unit (.first (.second (.loadCell (.var 3))))))
        (LanguageResult.success (.inRight .unit (.var 0))))
      (.inRight .word snapshot) lookupStore)
    (failed : Evaluates (snapshot :: found :: .word position :: .cellRef elementType arrayLocation :: environment)
      lookupStore (shift 4 value) (.inLeft rightType (.word reason)) final) :
    Evaluates environment store
      (code slot storedType outputType invalid comparison.expression value next (some modifier) layout index)
      (.inLeft outputType (.word reason)) final :=
  compound_prefix reference full indexed read within lookedUp snapshotted (LanguageResult.bind_failure _ failed)

theorem compound_modified_failure {right : Value} {reason : Word} {rhsStore final : Store}
    (reference : environment[slot]? = some (.cellRef cellType location))
    (full : store.read? location = some (.inRight leftType (.cellRef elementType arrayLocation)))
    (indexed : Evaluates (.cellRef elementType arrayLocation :: environment) store (shift 1 index)
      (.inRight .word (.word position)) after)
    (read : after.read? arrayLocation = some (.pair (.word length) rest)) (within : position < length)
    (lookedUp : Evaluates (.word position :: .cellRef elementType arrayLocation :: environment) after
      (OrderedMapping.lookup layout comparison.expression (.second (.second (.loadCell (.var 1)))) (.var 0))
      (.inRight .word found) lookupStore)
    (snapshotted : Evaluates (found :: .word position :: .cellRef elementType arrayLocation :: environment) lookupStore
      (.caseE (.var 0) (LanguageResult.success (.inRight .unit (.first (.second (.loadCell (.var 3))))))
        (LanguageResult.success (.inRight .unit (.var 0))))
      (.inRight .word snapshot) lookupStore)
    (rhsEvaluated : Evaluates (snapshot :: found :: .word position :: .cellRef elementType arrayLocation :: environment)
      lookupStore (shift 4 value) (.inRight .word right) rhsStore)
    (failed : Evaluates
      (right :: snapshot :: found :: .word position :: .cellRef elementType arrayLocation :: environment) rhsStore
      (modified modifier.leafType modifier.operator modifier.bitNot (.var 1) (.var 0) modifier.invalidOperand
        modifier.wrap)
      (.inLeft modifier.leafType (.word reason)) final) :
    Evaluates environment store
      (code slot storedType outputType invalid comparison.expression value next (some modifier) layout index)
      (.inLeft outputType (.word reason)) final :=
  compound_prefix reference full indexed read within lookedUp snapshotted
    (LanguageResult.bind_success _ rhsEvaluated (LanguageResult.bind_failure _ failed))

end Compound

/-- A compound write or a `~` below the array's length: the snapshot, the right side and `modified`'s leaf,
then the insert of the leaf at the index; after `guard`'s check the array's cell takes the updated entries,
keeping its length and default element, and `next` runs with the eight binders. `guarded` is `guard`'s
passing check, as `DataPlaceExecution.execute_success` takes it. -/
theorem compound_evaluates {checked : SourceCoreCompatibleCatalog.Checked} {fuel : Nat}
    {comparison : SourceCoreCompatibleDataEquality.Prepared checked}
    (prepared : SourceCoreCompatibleDataEquality.prepare fuel checked (.constructor (.builtin .word)) = .ok comparison)
    {layout : OrderedMapping.Layout} (keyType : layout.keyType = .word)
    {environment : Environment} {store : Store} {slot : Nat} {storedType outputType cellType : Ty} {invalid : Word}
    {value next index : Expr} {location : Location} {leftType elementType : Ty} {arrayLocation : Location}
    {position length : Word} {rest found snapshot right changed length' default result : Value}
    {modifier : ElementModifier} {entries : OrderedMapping.Entries}
    {after lookupStore rhsStore modifiedStore final : Store}
    (reference : environment[slot]? = some (.cellRef cellType location))
    (full : store.read? location = some (.inRight leftType (.cellRef elementType arrayLocation)))
    (indexed : Evaluates (.cellRef elementType arrayLocation :: environment) store (shift 1 index)
      (.inRight .word (.word position)) after)
    (read : after.read? arrayLocation = some (.pair (.word length) rest)) (within : position < length)
    (lookedUp : Evaluates (.word position :: .cellRef elementType arrayLocation :: environment) after
      (OrderedMapping.lookup layout comparison.expression (.second (.second (.loadCell (.var 1)))) (.var 0))
      (.inRight .word found) lookupStore)
    (snapshotted : Evaluates (found :: .word position :: .cellRef elementType arrayLocation :: environment) lookupStore
      (.caseE (.var 0) (LanguageResult.success (.inRight .unit (.first (.second (.loadCell (.var 3))))))
        (LanguageResult.success (.inRight .unit (.var 0))))
      (.inRight .word snapshot) lookupStore)
    (rhsEvaluated : Evaluates (snapshot :: found :: .word position :: .cellRef elementType arrayLocation :: environment)
      lookupStore (shift 4 value) (.inRight .word right) rhsStore)
    (modifiedEvaluated : Evaluates
      (right :: snapshot :: found :: .word position :: .cellRef elementType arrayLocation :: environment) rhsStore
      (modified modifier.leafType modifier.operator modifier.bitNot (.var 1) (.var 0) modifier.invalidOperand
        modifier.wrap)
      (.inRight .word changed) modifiedStore)
    (current : modifiedStore.read? arrayLocation =
      some (.pair length' (.pair default (OrderedMapping.encode layout entries))))
    (wordKeys : ∀ key value, (key, value) ∈ entries → ∃ word, key = .word word)
    (guarded : ∀ {result : Value} {final : Store},
      Evaluates
        (OrderedMapping.encode layout
            (OrderedMapping.insertEntries GenericHeap.arrayKeyEqual (.word position) changed entries) ::
          changed :: right :: snapshot :: found :: .word position :: .cellRef elementType arrayLocation :: environment)
        (CompatibleMappingComparison.insertStore comparison layout
          (changed :: right :: snapshot :: found :: .word position :: .cellRef elementType arrayLocation :: environment)
          modifiedStore entries (.word position) changed)
        (.letE (.storeCell (.var 6) (.pair (.first (.loadCell (.var 6)))
            (.pair (.first (.second (.loadCell (.var 6)))) (.var 0))))
          (shift 8 next)) result final →
      Evaluates
        (OrderedMapping.encode layout
            (OrderedMapping.insertEntries GenericHeap.arrayKeyEqual (.word position) changed entries) ::
          changed :: right :: snapshot :: found :: .word position :: .cellRef elementType arrayLocation :: environment)
        (CompatibleMappingComparison.insertStore comparison layout
          (changed :: right :: snapshot :: found :: .word position :: .cellRef elementType arrayLocation :: environment)
          modifiedStore entries (.word position) changed)
        (SourceCoreDataPlaces.guard outputType modifier.operator
          (.letE (.storeCell (.var 6) (.pair (.first (.loadCell (.var 6)))
              (.pair (.first (.second (.loadCell (.var 6)))) (.var 0))))
            (shift 8 next))) result final)
    (nextEvaluated : Evaluates
      (.unit :: OrderedMapping.encode layout
          (OrderedMapping.insertEntries GenericHeap.arrayKeyEqual (.word position) changed entries) ::
        changed :: right :: snapshot :: found :: .word position :: .cellRef elementType arrayLocation :: environment)
      ((CompatibleMappingComparison.insertStore comparison layout
          (changed :: right :: snapshot :: found :: .word position :: .cellRef elementType arrayLocation :: environment)
          modifiedStore entries (.word position) changed).set arrayLocation
        (.pair length' (.pair default (OrderedMapping.encode layout
          (OrderedMapping.insertEntries GenericHeap.arrayKeyEqual (.word position) changed entries)))))
      (shift 8 next) result final) :
    Evaluates environment store
      (code slot storedType outputType invalid comparison.expression value next (some modifier) layout index)
      result final := by
  apply LanguageResult.bind_success _ (root_full reference full)
  simp only [arrayElementWrite]
  apply LanguageResult.bind_success _ indexed
  apply Evaluates.ifTrue (within_check read within)
  simp only [elementStore]
  rw [shift_closed comparison, shift_closed comparison]
  apply LanguageResult.bind_success _ lookedUp (LanguageResult.bind_success _ snapshotted
    (LanguageResult.bind_success _ rhsEvaluated (LanguageResult.bind_success _ modifiedEvaluated _)))
  let stack :=
    changed :: right :: snapshot :: found :: .word position :: .cellRef elementType arrayLocation :: environment
  have inserted := OrderedMapping.insert_evaluates (environment := stack)
    (mapping := .second (.second (.loadCell (.var 5)))) (keyExpr := .var 4) (valueExpr := .var 0)
    (keyEqual := comparison.expression) entries (.word position) changed
    (CompatibleMappingComparison.comparator comparison stack modifiedStore) GenericHeap.arrayKeyEqual
    (.second (.second (.loadCell (.var rfl) current))) (.var rfl) (.var rfl)
    (CompatibleEquality.prepared_evaluates_exact comparison stack modifiedStore)
    (CompatibleArrayEvaluation.word_comparisons prepared keyType stack modifiedStore wordKeys position _)
  apply LanguageResult.bind_success _ inserted
  have bound : arrayLocation < modifiedStore.length := (List.getElem?_eq_some_iff.mp current).1
  have kept : (CompatibleMappingComparison.insertStore comparison layout stack modifiedStore entries (.word position)
      changed).read? arrayLocation = some (.pair length' (.pair default (OrderedMapping.encode layout entries))) := by
    simp only [CompatibleMappingComparison.insertStore, OrderedMapping.installedStore, WordMapping.installedStore,
      CompatibleMappingComparison.comparisonStore, Store.read?, List.append_assoc] at current ⊢
    rw [List.getElem?_append_left bound]
    exact current
  have keptBound : arrayLocation <
      (CompatibleMappingComparison.insertStore comparison layout stack modifiedStore entries (.word position)
        changed).length :=
    (List.getElem?_eq_some_iff.mp kept).1
  exact guarded (.letE (.storeCell (.var rfl) kept
    (.pair (.first (.loadCell (.var rfl) kept)) (.pair (.first (.second (.loadCell (.var rfl) kept))) (.var rfl)))
    (write_at keptBound _)) nextEvaluated)

/-! ### Renaming

A renaming of the code renames the root's slot, the index, the right side and the continuation; the
comparison is closed, and `modified` and `guard` name only the write's own binders. -/

private theorem modified_rename (type : Ty) (operator : Option Frontend.SourceCoreDataPlaces.Modifier) (bitNot : Bool)
    (invalid : Word) (ξ : Renaming) {wrap : Option TypeSystem.FixedInteger} :
    (modified type operator bitNot (.var 1) (.var 0) invalid wrap).rename ξ.lift.lift =
      modified type operator bitNot (.var 1) (.var 0) invalid wrap := by
  rcases wrap with _ | wrapType
  · cases bitNot <;> cases operator <;> simp [modified, LanguageResult.success, LanguageResult.failure,
      shift, List.range, List.range.loop, List.foldl, Expr.weakenAt, Expr.rename, Renaming.lift]
  · by_cases signed : wrapType.signed = true <;> cases bitNot <;> cases operator <;>
      simp [modified, signed, LanguageResult.success, LanguageResult.failure,
        shift, List.range, List.range.loop, List.foldl, Expr.weakenAt, Expr.rename, Renaming.lift]

theorem code_rename {checked : SourceCoreCompatibleCatalog.Checked}
    (comparison : SourceCoreCompatibleDataEquality.Prepared checked) (slot : Nat) (storedType outputType : Ty)
    (invalid : Word) (value next : Expr) (modifier : Option ElementModifier) (layout : OrderedMapping.Layout)
    (index : Expr) (ξ : Renaming) :
    (code slot storedType outputType invalid comparison.expression value next modifier layout index).rename ξ =
      code (ξ slot) storedType outputType invalid comparison.expression (value.rename ξ) (next.rename ξ) modifier
        layout (index.rename ξ) := by
  have closed : ∀ ρ : Renaming, comparison.expression.rename ρ = comparison.expression :=
    fun ρ => CoreProof.closed_rename comparison.typed ρ
  cases modifier <;> simp [code, arrayElementWrite, elementStore, LanguageResult.bind, LanguageResult.success,
    LanguageResult.failure, shift, List.range, List.range.loop, List.foldl, Expr.rename, Renaming.lift,
    CompatibleArrayEvaluation.ordered_insert_rename, CompatibleArrayEvaluation.ordered_lookup_rename,
    closed, CompatibleMapping.Transport.expression_weaken, modified_rename, DataPlaceGuard.rename_lift]

/-! ### The receipt

`lowerElements` at one element, inverted: the root's binder, its cell and the array's Core cell type,
the word comparison, the index's and the right side's code, and the code `code` builds. -/

section Receipt
open SourceInference DataPlaceCertificates

private theorem bind_ok {α β ε : Type} {computation : Except ε α} {next : α → Except ε β}
    {result : β} (accepted : computation >>= next = .ok result) :
    ∃ value, computation = .ok value ∧ next value = .ok result := by
  cases computation with
  | error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

private theorem ensureType_ok {site : SourceCoreElaboration.ErrorSite} {expected actual : Ty} {done : Unit}
    (accepted : SourceCoreBasic.ensureType site expected actual = .ok done) : expected = actual := by
  unfold SourceCoreBasic.ensureType at accepted
  split at accepted
  · assumption
  · cases accepted

/-- The modifier `lowerElements` gives an element: none for a plain write, else the route's own. -/
def modifierOf (assignment : AssignmentResolution) (operator : Syntax.ValueAssignOp) (bitNot : Bool) (leafType : Ty)
    (invalidOperand : Word) : Option ElementModifier :=
  if operator = .equal ∧ !bitNot then none
  else some ⟨leafType, placeModifier assignment.target.type (leafType = .integer) operator bitNot, bitNot,
    invalidOperand, SourceCoreDataPlaces.placeWrap assignment.target.type operator bitNot⟩

/-- The receipt of a write to one element. -/
inductive Generated (context : SourceCoreCompatibleDataPlaces.Context)
    (expression : SourceCoreCompatibleDataPlaces.ExpressionLowerer) (fuel : Nat) (source : TypedSource)
    (scope : SourceCoreLocalCell.Scope) (site : SourceCoreElaboration.ErrorSite) (assignment : AssignmentResolution)
    (operator : Syntax.ValueAssignOp) (rhs : Option ExpressionId) (outputType : Ty) (next : Expr)
    (reasonAt : ExpressionId → Word) (invalidProjection invalidOperand : Word) (key : ExpressionId) : Expr → Prop where
  | intro (binder : TypedBinder) (slot : Nat) (comparison : SourceCoreCompatibleDataEquality.Prepared context.checked)
      (keyCode : SourceCoreBasic.LoweredExpr) (elementType : Ty) (identity : DataTypeId) (value : Expr)
      (requirements : assignment.requirements.isEmpty = true)
      (rooted : rootBinder source assignment.target.root = .ok binder)
      (projected : project context.checked (.binder assignment.target.root) binder.scheme.body =
        .ok (.cell (.product .word (.product elementType (.namedData identity)))))
      (lookup : SourceCoreLocalCell.lookup? scope assignment.target.root =
        some (slot, .cell (.product .word (.product elementType (.namedData identity)))))
      (preparedBy : SourceCoreCompatibleDataEquality.prepare fuel context.checked (.constructor (.builtin .word)) =
        .ok comparison)
      (keyGenerated : expression fuel source scope key reasonAt = .ok keyCode) (keyType : keyCode.type = .word)
      (leaf : project context.checked site assignment.target.type = .ok elementType)
      (operatorValid : operator = .equal ∧ rhs.isNone = false ∨ elementType = .word ∨
        elementType = .integer ∧ operator.wordOnly = false)
      (rhsGenerated : RhsGenerated expression fuel source scope reasonAt elementType rhs value) :
      Generated context expression fuel source scope site assignment operator rhs outputType next reasonAt
        invalidProjection invalidOperand key
        (code slot (.cell (.product .word (.product elementType (.namedData identity)))) outputType invalidProjection
          comparison.expression value next (modifierOf assignment operator rhs.isNone elementType invalidOperand)
          ⟨.word, elementType, identity⟩ keyCode.expression)

theorem generated_of_lower {context : SourceCoreCompatibleDataPlaces.Context}
    {expression : SourceCoreCompatibleDataPlaces.ExpressionLowerer} {fuel : Nat} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {site : SourceCoreElaboration.ErrorSite} {assignment : AssignmentResolution}
    {operator : Syntax.ValueAssignOp} {rhs : Option ExpressionId} {outputType : Ty} {next : Expr}
    {reasonAt : ExpressionId → Word} {invalidProjection invalidOperand : Word} {key : ExpressionId} {lowered : Expr}
    (single : assignment.target.projections = [.element key])
    (accepted : lowerElements context expression fuel source scope site assignment operator rhs outputType next reasonAt
      invalidProjection invalidOperand = .ok lowered) :
    Generated context expression fuel source scope site assignment operator rhs outputType next reasonAt
      invalidProjection invalidOperand key lowered := by
  unfold lowerElements at accepted
  dsimp only at accepted
  split at accepted
  case isFalse => simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at accepted
  rename_i requirements
  obtain ⟨binder, rooted, accepted⟩ := bind_ok accepted
  obtain ⟨rootType, projected, accepted⟩ := bind_ok accepted
  cases lookup : SourceCoreLocalCell.lookup? scope assignment.target.root with
  | none => simp [lookup, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at accepted
  | some pair =>
    obtain ⟨slot, storedType⟩ := pair
    simp only [lookup, pure, Except.pure, bind, Except.bind] at accepted
    rw [single] at accepted
    simp only [List.foldlM] at accepted
    cases typed : SourceCoreBasic.ensureType site rootType storedType with
    | error => simp [typed] at accepted
    | ok checkedUnit =>
      have same := ensureType_ok typed
      subst storedType
      simp only [typed] at accepted
      cases preparedBy :
          SourceCoreCompatibleDataEquality.prepare fuel context.checked (.constructor (.builtin .word)) with
      | error => simp [preparedBy, Except.mapError] at accepted
      | ok comparison =>
        simp only [preparedBy, Except.mapError] at accepted
        split at accepted
        · cases accepted
        rename_i stepResult stepped
        obtain ⟨stepValue, stepRun, stepPure⟩ := bind_ok stepped
        cases stepPure
        split at stepRun
        case h_2 => cases stepRun
        rename_i elementType identity
        cases keyGenerated : expression fuel source scope key reasonAt with
        | error => rw [keyGenerated] at stepRun; cases stepRun
        | ok keyCode =>
          rw [keyGenerated] at stepRun
          dsimp only at stepRun
          cases keyTyped : SourceCoreBasic.ensureType site .word keyCode.type with
          | error => rw [keyTyped] at stepRun; cases stepRun
          | ok keyUnit =>
            rw [keyTyped] at stepRun
            cases stepRun
            have keyType := ensureType_ok keyTyped
            cases leaf : project context.checked site assignment.target.type with
            | error => simp [leaf] at accepted
            | ok leafType =>
              simp only [leaf] at accepted
              cases leafTyped : SourceCoreBasic.ensureType site leafType elementType with
              | error => simp [leafTyped] at accepted
              | ok leafUnit =>
                have leafSame := ensureType_ok leafTyped
                subst leafType
                simp only [leafTyped] at accepted
                have finish (operatorValid : operator = .equal ∧ rhs.isNone = false ∨ elementType = .word ∨
                      elementType = .integer ∧ operator.wordOnly = false)
                    (completed : (match rhs with
                      | none => Except.ok (LanguageResult.bind outputType
                          ((Expr.var slot).loadCell.caseE
                            (LanguageResult.failure (Ty.word.product (elementType.product (Ty.namedData identity))).cell
                              (Expr.word invalidProjection))
                            (LanguageResult.success (Expr.var 0)))
                          (arrayElementWrite outputType comparison.expression (LanguageResult.success Expr.unit) next
                            (modifierOf assignment operator rhs.isNone elementType invalidOperand) 1
                            [(⟨.word, elementType, identity⟩, keyCode.expression)]))
                      | some id => do
                          let value ← expression fuel source scope id reasonAt
                          SourceCoreBasic.ensureType site elementType value.type
                          pure (LanguageResult.bind outputType
                            ((Expr.var slot).loadCell.caseE
                              (LanguageResult.failure
                                (Ty.word.product (elementType.product (Ty.namedData identity))).cell
                                (Expr.word invalidProjection))
                              (LanguageResult.success (Expr.var 0)))
                            (arrayElementWrite outputType comparison.expression value.expression next
                              (modifierOf assignment operator rhs.isNone elementType invalidOperand) 1
                              [(⟨.word, elementType, identity⟩, keyCode.expression)]))) = .ok lowered) :
                    Generated context expression fuel source scope site assignment operator rhs outputType next
                      reasonAt invalidProjection invalidOperand key lowered := by
                  cases rhs with
                  | none =>
                    simp only [Except.ok.injEq] at completed
                    subst lowered
                    exact .intro binder slot comparison keyCode elementType identity _ requirements rooted projected
                      lookup preparedBy keyGenerated keyType.symm leaf operatorValid .absent
                  | some id =>
                    obtain ⟨value, valueGenerated, completed⟩ := bind_ok completed
                    obtain ⟨valueUnit, valueTyped, completed⟩ := bind_ok completed
                    simp only [pure, Except.pure, Except.ok.injEq] at completed
                    subst lowered
                    exact .intro binder slot comparison keyCode elementType identity _ requirements rooted projected
                      lookup preparedBy keyGenerated keyType.symm leaf operatorValid
                      (.present valueGenerated (ensureType_ok valueTyped))
                split at accepted
                · rename_i checkNeeded
                  split at accepted
                  · rename_i leafOk
                    simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, Bool.not_eq_true'] at leafOk
                    exact finish (.inr leafOk) (by
                      cases rhs <;> simpa [modifierOf, bind, Except.bind, pure, Except.pure] using accepted)
                  · cases accepted
                · rename_i noCheck
                  simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, Decidable.not_not, Bool.not_eq_true] at noCheck
                  exact finish (.inl noCheck) (by
                    cases rhs <;> simpa [modifierOf, bind, Except.bind, pure, Except.pure] using accepted)

end Receipt

end Solcore.SourceSemantics.CoreLowering.CompatibleElementWrites
