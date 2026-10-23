import Solcore.Frontend.RustHull.Semantics
import Solcore.Frontend.RustHull.LoweringSupport
import Solcore.Core.Store
import Solcore.Core.Renaming

/-! Representation of independently defined Hull values and mutable locals.
Core may contain additional function and loop cells. Source locations are
therefore related through an explicit layout instead of identifying the heaps.
The relation does not invoke the lowerer or the Core evaluator. -/
set_option autoImplicit false

namespace Solcore.Frontend.RustHull.Correspondence

inductive ValueRel : Core.Ty → Semantics.Value → Core.Value → Prop where
  | word (value : Core.Word) : ValueRel .word (.word value) (.word value)
  | bool (value : Bool) : ValueRel .bool (.bool value) (.bool value)
  | unit : ValueRel .unit .unit .unit
  | pair {leftType rightType : Core.Ty} {left right : Semantics.Value}
      {coreLeft coreRight : Core.Value}
      (leftRelated : ValueRel leftType left coreLeft) (rightRelated : ValueRel rightType right coreRight) :
      ValueRel (.product leftType rightType) (.pair left right) (.pair coreLeft coreRight)
  | inl {leftType rightType : Core.Ty} {value : Semantics.Value} {coreValue : Core.Value}
      (payload : ValueRel leftType value coreValue) :
      ValueRel (.sum leftType rightType) (.inl value) (.inLeft rightType coreValue)
  | inr {leftType rightType : Core.Ty} {value : Semantics.Value} {coreValue : Core.Value}
      (payload : ValueRel rightType value coreValue) :
      ValueRel (.sum leftType rightType) (.inr value) (.inRight leftType coreValue)

/-- Malformed source observations have no Core representation. Language
failures retain their exact reason word, while successful payloads are typed. -/
inductive ResultRel (type : Core.Ty) : Semantics.Result Semantics.Value → Core.Value → Prop where
  | value {source : Semantics.Value} {target : Core.Value} (related : ValueRel type source target) :
      ResultRel type (.value source) (.inRight .word target)
  | language (reason : Core.Word) :
      ResultRel type (.fault (.language reason)) (.inLeft type (.word reason))

/-- Each source heap index records its value layout and Core cell location. -/
abbrev World := List (Core.Ty × Nat)

structure HeapRel (world : World) (source : Semantics.Heap) (target : Core.Store) : Prop where
  length_eq : world.length = source.length
  cell : ∀ (index : Nat) (type : Core.Ty) (location : Nat), world[index]? = some (type, location) →
    ∃ sourceValue targetValue, source[index]? = some sourceValue ∧
      target.read? location = some (.inRight .unit targetValue) ∧
      ValueRel type sourceValue targetValue
  distinct : ∀ (left right : Nat) (leftType rightType : Core.Ty) (location : Nat),
    world[left]? = some (leftType, location) →
    world[right]? = some (rightType, location) → left = right

/-- Both lookups come from the actual source derivation and accepted lowering.
Administrative function bindings need not occur in the source environment.
`rename` tracks Core binders introduced by sequencing and control flow. -/
def EnvironmentRel (world : World) (source : Semantics.Environment) (scope : Scope)
    (rename : Nat → Nat) (target : Core.Environment) : Prop :=
  ∀ name sourceLocation binding index,
    Semantics.lookupLocation source name = some sourceLocation →
    scope.lookup name = .ok (binding, index) →
    ∃ location, world[sourceLocation]? = some (binding.type, location) ∧
      binding.reference = true ∧
      target[rename index]? = some (.cellRef (Core.OptionalCell.cellType binding.type) location)

theorem ValueRel.functional {type : Core.Ty} {source : Semantics.Value}
    {left right : Core.Value} (leftRel : ValueRel type source left)
    (rightRel : ValueRel type source right) : left = right := by
  induction leftRel generalizing right with
  | word => cases rightRel; rfl
  | bool => cases rightRel; rfl
  | unit => cases rightRel; rfl
  | pair _ _ leftIH rightIH =>
      cases rightRel with
      | pair left right => rw [leftIH left, rightIH right]
  | inl _ ih => cases rightRel with | inl payload => rw [ih payload]
  | inr _ ih => cases rightRel with | inr payload => rw [ih payload]

theorem ValueRel.pair_inv {leftType rightType : Core.Ty} {source : Semantics.Value}
    {left right : Core.Value} (related : ValueRel (.product leftType rightType) source (.pair left right)) :
    ∃ sourceLeft sourceRight, source = .pair sourceLeft sourceRight ∧
      ValueRel leftType sourceLeft left ∧ ValueRel rightType sourceRight right := by
  cases related with | pair left right => exact ⟨_, _, rfl, left, right⟩

theorem ValueRel.inl_inv {leftType rightType : Core.Ty} {source : Semantics.Value}
    {value : Core.Value} (related : ValueRel (.sum leftType rightType) source (.inLeft rightType value)) :
    ∃ payload, source = .inl payload ∧ ValueRel leftType payload value := by
  cases related with | inl payload => exact ⟨_, rfl, payload⟩

theorem ValueRel.inr_inv {leftType rightType : Core.Ty} {source : Semantics.Value}
    {value : Core.Value} (related : ValueRel (.sum leftType rightType) source (.inRight leftType value)) :
    ∃ payload, source = .inr payload ∧ ValueRel rightType payload value := by
  cases related with | inr payload => exact ⟨_, rfl, payload⟩

theorem HeapRel.empty (store : Core.Store) : HeapRel [] [] store where
  length_eq := rfl
  cell := by intros; contradiction
  distinct := by intros; contradiction

theorem HeapRel.read {world : World} {source : Semantics.Heap} {target : Core.Store}
    (related : HeapRel world source target) {index : Nat} {type : Core.Ty} {location : Nat}
    (entry : world[index]? = some (type, location)) {sourceValue : Semantics.Value}
    (found : source[index]? = some sourceValue) :
    ∃ targetValue, target.read? location = some (.inRight .unit targetValue) ∧
      ValueRel type sourceValue targetValue := by
  obtain ⟨other, value, sourceFound, coreFound, valueRelated⟩ := related.cell index type location entry
  have equal : other = sourceValue := Option.some.inj (sourceFound.symm.trans found)
  subst other
  exact ⟨value, coreFound, valueRelated⟩

theorem HeapRel.location_bound {world : World} {source : Semantics.Heap} {target : Core.Store}
    (related : HeapRel world source target) {index : Nat} {type : Core.Ty} {location : Nat}
    (entry : world[index]? = some (type, location)) : location < target.length := by
  obtain ⟨_, _, _, found, _⟩ := related.cell index type location entry
  exact (List.getElem?_eq_some_iff.mp found).1

/-- Function and loop-cell allocation leaves all source cells in place. -/
theorem HeapRel.appendCore {world : World} {source : Semantics.Heap} {target : Core.Store}
    (related : HeapRel world source target) (suffix : Core.Store) :
    HeapRel world source (target ++ suffix) where
  length_eq := related.length_eq
  distinct := related.distinct
  cell := by
    intro index type location entry
    obtain ⟨sourceValue, targetValue, sourceFound, coreFound, valueRelated⟩ :=
      related.cell index type location entry
    refine ⟨sourceValue, targetValue, sourceFound, ?_, valueRelated⟩
    simpa only [Core.Store.read?, List.getElem?_append_left (related.location_bound entry)] using coreFound

/-- Assignment updates exactly the source cell represented by the actual Core
write. Distinct represented locations protect every other source binding. -/
theorem HeapRel.write {world : World} {source : Semantics.Heap} {target updated : Core.Store}
    (related : HeapRel world source target) {index : Nat} {type : Core.Ty} {location : Nat}
    (entry : world[index]? = some (type, location))
    {sourceValue : Semantics.Value} {targetValue : Core.Value}
    (valueRelated : ValueRel type sourceValue targetValue)
    (written : target.write? location (.inRight .unit targetValue) = some updated) :
    HeapRel world (source.set index sourceValue) updated where
  length_eq := by simpa using related.length_eq
  distinct := related.distinct
  cell := by
    intro other otherType otherLocation otherEntry
    by_cases same : other = index
    · subst other
      have equal := Option.some.inj (otherEntry.symm.trans entry)
      cases equal
      refine ⟨sourceValue, targetValue, ?_, Core.Store.write?_reads_written written, valueRelated⟩
      apply List.getElem?_set_self
      rw [← related.length_eq]
      exact (List.getElem?_eq_some_iff.mp entry).1
    · obtain ⟨oldSource, oldTarget, sourceFound, coreFound, oldRelated⟩ :=
        related.cell other otherType otherLocation otherEntry
      refine ⟨oldSource, oldTarget, ?_, ?_, oldRelated⟩
      · simpa only [List.getElem?_set_ne (Ne.symm same)] using sourceFound
      · have different : otherLocation ≠ location := by
          intro equal
          subst otherLocation
          exact same (related.distinct other index otherType type location otherEntry entry)
        rw [Core.Store.write?_preserves_other written different]
        exact coreFound

/-- Source allocation and the actual Core allocation may choose different
numeric locations. The extended world records both fresh locations exactly. -/
theorem HeapRel.allocate {world : World} {source : Semantics.Heap} {target : Core.Store}
    (related : HeapRel world source target) {type : Core.Ty}
    {sourceValue : Semantics.Value} {targetValue : Core.Value}
    (valueRelated : ValueRel type sourceValue targetValue) :
    HeapRel (world ++ [(type, target.length)]) (source ++ [sourceValue])
      (target ++ [.inRight .unit targetValue]) where
  length_eq := by simpa using related.length_eq
  cell := by
    intro index entryType location entry
    by_cases old : index < world.length
    · rw [List.getElem?_append_left old] at entry
      exact (related.appendCore [.inRight .unit targetValue]).cell index entryType location entry
        |>.imp fun oldSource proof => by
          obtain ⟨oldTarget, found, targetFound, oldRelated⟩ := proof
          refine ⟨oldTarget, ?_, targetFound, oldRelated⟩
          rw [List.getElem?_append_left (by simpa only [related.length_eq] using old)]
          exact found
    · have bounds := (List.getElem?_eq_some_iff.mp entry).1
      have fresh : index = world.length := by simp only [List.length_append, List.length_singleton] at bounds; omega
      subst index
      simp only [List.getElem?_concat_length, Option.some.injEq, Prod.mk.injEq] at entry
      obtain ⟨rfl, rfl⟩ := entry.symm
      refine ⟨sourceValue, targetValue, ?_, ?_, valueRelated⟩
      · rw [related.length_eq, List.getElem?_concat_length]
      · exact List.getElem?_concat_length
  distinct := by
    intro left right leftType rightType location leftEntry rightEntry
    have leftBound := (List.getElem?_eq_some_iff.mp leftEntry).1
    have rightBound := (List.getElem?_eq_some_iff.mp rightEntry).1
    simp only [List.length_append, List.length_singleton] at leftBound rightBound
    by_cases leftOld : left < world.length
    · rw [List.getElem?_append_left leftOld] at leftEntry
      by_cases rightOld : right < world.length
      · rw [List.getElem?_append_left rightOld] at rightEntry
        exact related.distinct left right leftType rightType location leftEntry rightEntry
      · have fresh : right = world.length := by omega
        subst right
        simp only [List.getElem?_concat_length, Option.some.injEq, Prod.mk.injEq] at rightEntry
        have bound := related.location_bound leftEntry
        omega
    · have fresh : left = world.length := by omega
      subst left
      by_cases rightOld : right < world.length
      · rw [List.getElem?_append_left rightOld] at rightEntry
        simp only [List.getElem?_concat_length, Option.some.injEq, Prod.mk.injEq] at leftEntry
        have bound := related.location_bound rightEntry
        omega
      · omega

theorem EnvironmentRel.extendWorld {world : World} {source : Semantics.Environment} {scope : Scope}
    {rename : Nat → Nat} {target : Core.Environment}
    (related : EnvironmentRel world source scope rename target) (suffix : World) :
    EnvironmentRel (world ++ suffix) source scope rename target := by
  intro name sourceLocation binding index found lookup
  obtain ⟨location, entry, reference, value⟩ := related name sourceLocation binding index found lookup
  refine ⟨location, ?_, reference, value⟩
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp entry).1]
  exact entry

theorem scope_lookup_cons (head : Binding) (scope : Scope) (name : String) :
    Scope.lookup (head :: scope) name =
      if head.name == some name then .ok (head, 0)
      else match scope.lookup name with
        | .error error => .error error
        | .ok (binding, index) => .ok (binding, index + 1) := by
  simp only [Scope.lookup, List.zipIdx_cons', List.find?_cons, List.find?_map,
    Function.comp_def, Prod.map_fst, id_eq]
  cases head.name == some name <;> simp only [Bool.false_eq_true, ↓reduceIte]
  all_goals
    cases found : (scope.zipIdx.find? fun item => item.1.name == some name) with
    | none => rfl
    | some pair => cases pair; rfl

/-- The source local and Core optional-cell reference enter their lexical
environments together; previously named locals keep their shifted positions. -/
theorem EnvironmentRel.addLocal {world : World} {source : Semantics.Environment} {scope : Scope}
    {rename : Core.Renaming} {target : Core.Environment}
    (related : EnvironmentRel world source scope rename target)
    (name : String) (type : Core.Ty) (sourceLocation location : Nat)
    (entry : world[sourceLocation]? = some (type, location)) :
    EnvironmentRel world ((name, sourceLocation) :: source) (scope.addLocal name type)
      rename.lift (.cellRef (Core.OptionalCell.cellType type) location :: target) := by
  intro query sourceIndex binding index found lookup
  rw [Scope.addLocal, scope_lookup_cons] at lookup
  by_cases same : name = query
  · subst query
    simp only [beq_self_eq_true, ↓reduceIte, Except.ok.injEq, Prod.mk.injEq] at lookup
    obtain ⟨rfl, rfl⟩ := lookup.symm
    simp [Semantics.lookupLocation] at found
    subst sourceIndex
    exact ⟨location, entry, rfl, rfl⟩
  · simp only [Option.some_beq_some, beq_iff_eq, same, ↓reduceIte] at lookup
    cases old : scope.lookup query with
    | error error => simp only [old] at lookup; contradiction
    | ok pair =>
        rcases pair with ⟨oldBinding, oldIndex⟩
        simp only [old, Except.ok.injEq, Prod.mk.injEq] at lookup
        obtain ⟨rfl, rfl⟩ := lookup.symm
        have previous : Semantics.lookupLocation source query = some sourceIndex := by
          simpa [Semantics.lookupLocation, same] using found
        obtain ⟨oldLocation, oldEntry, reference, oldValue⟩ :=
          related query sourceIndex oldBinding oldIndex previous old
        exact ⟨oldLocation, oldEntry, reference, oldValue⟩

theorem EnvironmentRel.temporary {world : World} {source : Semantics.Environment} {scope : Scope}
    {rename : Core.Renaming} {target : Core.Environment}
    (related : EnvironmentRel world source scope rename target)
    (type : Core.Ty) (value : Core.Value) :
    EnvironmentRel world source (scope.temporary type) rename.lift (value :: target) := by
  intro name sourceLocation binding index found lookup
  rw [Scope.temporary, scope_lookup_cons] at lookup
  simp only [Option.none_beq_some, Bool.false_eq_true, ↓reduceIte] at lookup
  cases old : scope.lookup name with
  | error error => simp only [old] at lookup; contradiction
  | ok pair =>
      rcases pair with ⟨oldBinding, oldIndex⟩
      simp only [old, Except.ok.injEq, Prod.mk.injEq] at lookup
      obtain ⟨rfl, rfl⟩ := lookup.symm
      exact related name sourceLocation oldBinding oldIndex found old

/-- A real source read and a real compiler scope lookup identify the same
initialized Core cell, including the exact payload relation. -/
theorem EnvironmentRel.read {world : World} {sourceEnvironment : Semantics.Environment}
    {sourceHeap : Semantics.Heap} {scope : Scope} {rename : Core.Renaming}
    {targetEnvironment : Core.Environment} {targetStore : Core.Store}
    (environment : EnvironmentRel world sourceEnvironment scope rename targetEnvironment)
    (heap : HeapRel world sourceHeap targetStore) {name : String} {sourceLocation index : Nat}
    {binding : Binding} {sourceValue : Semantics.Value}
    (found : Semantics.lookupLocation sourceEnvironment name = some sourceLocation)
    (looked : scope.lookup name = .ok (binding, index))
    (read : sourceHeap[sourceLocation]? = some sourceValue) :
    ∃ location targetValue, binding.reference = true ∧
      targetEnvironment[rename index]? = some (.cellRef (Core.OptionalCell.cellType binding.type) location) ∧
      targetStore.read? location = some (.inRight .unit targetValue) ∧
      ValueRel binding.type sourceValue targetValue := by
  obtain ⟨location, entry, reference, target⟩ := environment name sourceLocation binding index found looked
  obtain ⟨value, cell, payload⟩ := heap.read entry read
  exact ⟨location, value, reference, target, cell, payload⟩

/-- Extra Core locals do not change source variable observations when the
compiler's variable renaming accounts for the added prefix. -/
theorem EnvironmentRel.prepend {world : World} {source : Semantics.Environment} {scope : Scope}
    {rename : Nat → Nat} {target : Core.Environment}
    (related : EnvironmentRel world source scope rename target) (extra : Core.Environment) :
    EnvironmentRel world source scope (fun index => extra.length + rename index) (extra ++ target) := by
  intro name sourceLocation binding index found lookup
  obtain ⟨location, entry, reference, value⟩ := related name sourceLocation binding index found lookup
  refine ⟨location, entry, reference, ?_⟩
  simpa only [List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left] using value

end Solcore.Frontend.RustHull.Correspondence
