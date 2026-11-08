import Solcore.Frontend.RustHull.Contract
import Solcore.Core.Fuel
import Solcore.Frontend.RustHull.Semantics
import Solcore.Frontend.RustHull.LoweringSupport
import Solcore.Core.Eval
import Solcore.Core.Internal.Renaming
import Solcore.Frontend.RustHull.Safety
import Solcore.Frontend.RustHull.Effects

/-!
# Lowering facts

Shapes of the lowering output, literal parsing, scope coverage, and the exact execution of a scalar
or contract receipt.
-/

section
-- leanmerge: from Solcore.Frontend.RustHull.ContractExecutionCorrespondence
/-! Actual contract receipt export and genuine checkpoint chains retain the
transition cost and result of the compiled runtime expression. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.Contract

theorem finish_not_checkpoint (limit : Nat) (value : Core.Value) (checkpoint : Core.State) :
    (finish limit value).outcome ≠ .outOfFuel checkpoint := by
  intro equality
  unfold finish at equality
  split at equality <;> try cases equality
  all_goals
    dsimp only at equality
    split at equality <;> try cases equality
  all_goals
    try split at equality <;> try cases equality
  all_goals
    conv at equality => lhs; whnf
    dsimp only [Pure.pure, Bind.bind] at equality
  repeat (any_goals (first | cases equality | split at equality))

theorem resumeWithReceipt_checkpoint_iff {start checkpoint : Core.State} {fuel limit : Nat} :
    (resumeWithReceipt start fuel limit).outcome = .outOfFuel checkpoint ↔
      Core.runStateful fuel start = .outOfFuel checkpoint := by
  cases executed : Core.runStateful fuel start with
  | done value store =>
      simp only [resumeWithReceipt, executed]
      exact iff_of_false (finish_not_checkpoint limit value checkpoint) (by intro impossible; cases impossible)
  | outOfFuel suspended => simp only [resumeWithReceipt, executed, Outcome.outOfFuel.injEq, Core.StatefulRunResult.outOfFuel.injEq]
  | fault error state => simp only [resumeWithReceipt, executed, reduceCtorEq]

/-- All steps use the checkpoint actually returned by the previous public
receipt, with a fixed export limit and cumulative additional fuel. -/
inductive ReceiptResumes (limit : Nat) : Receipt → Nat → Receipt → Prop where
  | refl (receipt : Receipt) : ReceiptResumes limit receipt 0 receipt
  | step {first previous : Receipt} {spent : Nat} {checkpoint : Core.State}
      (path : ReceiptResumes limit first spent previous)
      (exhausted : previous.outcome = .outOfFuel checkpoint) (additional : Nat) :
      ReceiptResumes limit first (spent + additional) (resumeWithReceipt checkpoint additional limit)

theorem ReceiptResumes.eq_combined_run {limit : Nat} {first last : Receipt} {additional : Nat}
    (path : ReceiptResumes limit first additional last) (prepared : Prepared) (fuel : Nat)
    (initial : first = runWithReceipt prepared fuel limit) :
    last = runWithReceipt prepared (fuel + additional) limit := by
  induction path with
  | refl => simpa only [Nat.add_zero] using initial
  | @step previous spent checkpoint path exhausted more ih =>
      have stopped := (resumeWithReceipt_checkpoint_iff).mp (ih.symm ▸ exhausted)
      simp only [runWithReceipt, resumeWithReceipt, Core.runStateful_resume stopped more, Nat.add_assoc]

theorem evaluation_run_complete {prepared : Prepared} {value : Core.Value} {store : Core.Store}
    (evaluation : Core.Evaluates [] [] prepared.expression value store) :
    ∃ required, ∀ fuel, required ≤ fuel → ∀ limit,
      runWithReceipt prepared fuel limit = finish limit value := by
  obtain ⟨required, completed⟩ := Core.evaluation_runStateful_complete_with_sufficient_fuel evaluation
  exact ⟨required, fun fuel enough limit => by
    simp only [runWithReceipt, resumeWithReceipt, completed fuel enough]⟩

theorem evaluation_resumes_exact {prepared : Prepared} {value : Core.Value} {store : Core.Store}
    (evaluation : Core.Evaluates [] [] prepared.expression value store) :
    ∃ required, ∀ fuel additional limit last,
      ReceiptResumes limit (runWithReceipt prepared fuel limit) additional last →
      (last = finish limit value ↔ required ≤ fuel + additional) ∧
      ((∃ checkpoint, last.outcome = .outOfFuel checkpoint) ↔ fuel + additional < required) := by
  obtain ⟨required, path⟩ := evaluation.toSteps
  refine ⟨required, ?_⟩
  intro fuel additional limit last resumed
  rw [resumed.eq_combined_run prepared fuel rfl]
  have exhausted : (∃ checkpoint, (runWithReceipt prepared (fuel + additional) limit).outcome = .outOfFuel checkpoint) ↔
      fuel + additional < required := by
    simpa only [runWithReceipt, resumeWithReceipt_checkpoint_iff] using path.runStateful_outOfFuel_iff (fuel := fuel + additional)
  refine ⟨⟨?_, ?_⟩, exhausted⟩
  · intro completed
    by_cases enough : required ≤ fuel + additional
    · exact enough
    exfalso
    obtain ⟨checkpoint, found⟩ := exhausted.mpr (by omega)
    rw [completed] at found
    exact finish_not_checkpoint limit value checkpoint found
  · intro enough
    simp only [runWithReceipt, resumeWithReceipt, path.runStateful_done_iff.mpr enough]

end Solcore.Frontend.RustHull.Contract
end

section
-- leanmerge: from Solcore.Frontend.RustHull.SemanticsCorrespondenceSupport
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
end

section
-- leanmerge: from Solcore.Frontend.RustHull.SemanticsTypeCorrespondence
/-! The actual type and zero-initializer translations agree with Hull's
independent layouts. Recursive references keep their specified opaque word
representation; successful lowering supplies the layout premise. -/
set_option autoImplicit false

namespace Solcore.Frontend.RustHull.Correspondence

def coreType : Semantics.Shape → Core.Ty
  | .word => .word
  | .bool => .bool
  | .unit => .unit
  | .product left right => .product (coreType left) (coreType right)
  | .sum left right => .sum (coreType left) (coreType right)

theorem coreType_injective : Function.Injective coreType := by
  intro left target same
  induction left generalizing target with
  | word => cases target <;> simp_all [coreType]
  | bool => cases target <;> simp_all [coreType]
  | unit => cases target <;> simp_all [coreType]
  | product left right leftIH rightIH =>
      cases target with
      | product otherLeft otherRight =>
          obtain ⟨a, b⟩ := Core.Ty.product.inj same
          rw [leftIH a, rightIH b]
      | _ => cases same
  | sum left right leftIH rightIH =>
      cases target with
      | sum otherLeft otherRight =>
          obtain ⟨a, b⟩ := Core.Ty.sum.inj same
          rw [leftIH a, rightIH b]
      | _ => cases same

theorem lowerType_shape {fuel : Nat} {type : Ty} {lowered : Core.Ty}
    (accepted : lowerType fuel type = .ok lowered) :
    ∃ shape, Semantics.shape type = some shape ∧ coreType shape = lowered := by
  induction fuel generalizing type lowered with
  | zero => simp [lowerType, fail] at accepted
  | succ fuel ih =>
      cases type with
      | word => cases accepted; exact ⟨.word, rfl, rfl⟩
      | bool => cases accepted; exact ⟨.bool, rfl, rfl⟩
      | unit => cases accepted; exact ⟨.unit, rfl, rfl⟩
      | namedRef name => cases accepted; exact ⟨.word, rfl, rfl⟩
      | named name inner => exact ih (type := inner) accepted
      | located span inner => exact ih (type := inner) accepted
      | function parameters result => simp [lowerType, fail] at accepted
      | product left right =>
          simp only [lowerType] at accepted
          obtain ⟨leftType, leftAccepted, accepted⟩ := lower_bind_eq_ok.mp accepted
          obtain ⟨rightType, rightAccepted, returned⟩ := lower_bind_eq_ok.mp accepted
          cases returned
          obtain ⟨leftShape, leftShapeEq, leftEq⟩ := ih leftAccepted
          obtain ⟨rightShape, rightShapeEq, rightEq⟩ := ih rightAccepted
          refine ⟨.product leftShape rightShape, ?_, ?_⟩
          · simp [Semantics.shape, leftShapeEq, rightShapeEq]
          · simp [coreType, leftEq, rightEq]
      | sum left right =>
          simp only [lowerType] at accepted
          obtain ⟨leftType, leftAccepted, accepted⟩ := lower_bind_eq_ok.mp accepted
          obtain ⟨rightType, rightAccepted, returned⟩ := lower_bind_eq_ok.mp accepted
          cases returned
          obtain ⟨leftShape, leftShapeEq, leftEq⟩ := ih leftAccepted
          obtain ⟨rightShape, rightShapeEq, rightEq⟩ := ih rightAccepted
          refine ⟨.sum leftShape rightShape, ?_, ?_⟩
          · simp [Semantics.shape, leftShapeEq, rightShapeEq]
          · simp [coreType, leftEq, rightEq]

theorem zeroValue_evaluates (shape : Semantics.Shape)
    {expression : Core.Expr} (accepted : zeroValue (coreType shape) = .ok expression)
    (environment : Core.Environment) (store : Core.Store) :
    ∃ value, ValueRel (coreType shape) shape.zero value ∧
      Core.Evaluates environment store expression value store := by
  induction shape generalizing expression with
  | word => cases accepted; exact ⟨_, .word _, .word⟩
  | bool => cases accepted; exact ⟨_, .bool _, .bool⟩
  | unit => cases accepted; exact ⟨_, .unit, .unit⟩
  | product left right leftIH rightIH =>
      simp only [coreType, zeroValue] at accepted
      obtain ⟨leftCode, leftAccepted, accepted⟩ := lower_bind_eq_ok.mp accepted
      obtain ⟨rightCode, rightAccepted, returned⟩ := lower_bind_eq_ok.mp accepted
      cases returned
      obtain ⟨leftValue, leftRel, leftEval⟩ := leftIH leftAccepted
      obtain ⟨rightValue, rightRel, rightEval⟩ := rightIH rightAccepted
      exact ⟨_, .pair leftRel rightRel, .pair leftEval rightEval⟩
  | sum left right leftIH _ =>
      simp only [coreType, zeroValue] at accepted
      obtain ⟨leftCode, leftAccepted, returned⟩ := lower_bind_eq_ok.mp accepted
      cases returned
      obtain ⟨value, related, evaluation⟩ := leftIH leftAccepted
      exact ⟨_, .inl related, .inLeft evaluation⟩

end Solcore.Frontend.RustHull.Correspondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.LiteralCorrespondence
/-! Literal parsing agrees with the independent Hull parser, including large
decimal and hexadecimal words reduced modulo 2^256. -/
set_option autoImplicit false

namespace Solcore.Frontend.RustHull.Correspondence

private theorem foldlM_some_of_ok {α β : Type}
    (step : β → α → LowerM β) (sourceStep : β → α → Option β)
    (agrees : ∀ state item next, step state item = .ok next → sourceStep state item = some next)
    (items : List α) {initial result : β}
    (accepted : items.foldlM step initial = .ok result) :
    items.foldlM sourceStep initial = some result := by
  induction items generalizing initial with
  | nil => cases accepted; rfl
  | cons item items ih =>
      simp only [List.foldlM_cons] at accepted ⊢
      obtain ⟨next, first, rest⟩ := lower_bind_eq_ok.mp accepted
      rw [agrees initial item next first]
      exact ih rest

private def digitValue (base : Nat) (char : Char) : Nat :=
  if '0' ≤ char && char ≤ '9' then char.toNat - '0'.toNat
  else if 'a' ≤ char && char ≤ 'f' then char.toNat - 'a'.toNat + 10
  else if 'A' ≤ char && char ≤ 'F' then char.toNat - 'A'.toNat + 10
  else base

private theorem digits_some_of_ok {base initial result : Nat} {digits : List Char} {text : String}
    (accepted : digits.foldlM (fun accumulator char =>
      if digitValue base char < base then
        pure ((accumulator * base + digitValue base char) % Core.wordModulus)
      else fail s!"invalid word literal: {text}") initial = .ok result) :
    digits.foldlM (fun accumulator char =>
      if digitValue base char < base then
        some ((accumulator * base + digitValue base char) % Core.wordModulus)
      else none) initial = some result := by
  apply foldlM_some_of_ok _ _ _ digits accepted
  intro state char next step
  by_cases valid : digitValue base char < base
  · rw [if_pos valid] at step ⊢
    cases step
    rfl
  · simp [valid, fail] at step

theorem parseWord_some_of_ok {text : String} {value : Core.Word}
    (accepted : parseWord text = .ok value) :
    Semantics.parseWord? text = some value := by
  unfold parseWord at accepted
  unfold Semantics.parseWord?
  dsimp only at accepted ⊢
  split at accepted <;> simp_all only
  all_goals
    split at accepted
    · simp [fail] at accepted
    · rename_i nonempty
      rw [if_neg nonempty]
      obtain ⟨number, parsed, returned⟩ := lower_bind_eq_ok.mp accepted
      cases returned
      have converted := digits_some_of_ok parsed
      exact congrArg (fun parsed : Option Nat =>
        parsed.bind fun value => some (Core.Word.ofNatModulo value)) converted

end Solcore.Frontend.RustHull.Correspondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.ScalarInputCorrespondence
/-! Actual public scalar arguments denote independent Hull values. The parser
constructs closed Core literals, whose evaluation preserves every input heap.
Arguments retain their source order and the compiler's unit/scalar/product
bundle convention. -/
set_option autoImplicit false

namespace Solcore.Frontend.RustHull.ScalarExecution
open Correspondence

inductive InputRel : Core.Ty → String → Semantics.Value → Prop where
  | word {input : String} {value : Core.Word} (parsed : Semantics.parseWord? input = some value) :
      InputRel .word input (.word value)
  | boolTrue : InputRel .bool "true" (.bool true)
  | boolFalse : InputRel .bool "false" (.bool false)
  | sumTrue : InputRel (.sum .unit .unit) "true" (.inr .unit)
  | sumFalse : InputRel (.sum .unit .unit) "false" (.inl .unit)
  | unit : InputRel .unit "unit" .unit

inductive InputsRel : List Core.Ty → List String → List Semantics.Value → Prop where
  | nil : InputsRel [] [] []
  | cons {type : Core.Ty} {types : List Core.Ty} {input : String} {inputs : List String}
      {value : Semantics.Value} {values : List Semantics.Value}
      (head : InputRel type input value) (tail : InputsRel types inputs values) :
      InputsRel (type :: types) (input :: inputs) (value :: values)

inductive ValuesRel : List Core.Ty → List Semantics.Value → List Core.Value → Prop where
  | nil : ValuesRel [] [] []
  | cons {type : Core.Ty} {types : List Core.Ty} {source : Semantics.Value}
      {sources : List Semantics.Value} {target : Core.Value} {targets : List Core.Value}
      (head : ValueRel type source target) (tail : ValuesRel types sources targets) :
      ValuesRel (type :: types) (source :: sources) (target :: targets)

def bundleValues : List Core.Value → Core.Value
  | [] => .unit
  | [value] => value
  | value :: rest => .pair value (bundleValues rest)

theorem ValuesRel.length {types : List Core.Ty} {sources : List Semantics.Value}
    {targets : List Core.Value} (related : ValuesRel types sources targets) :
    sources.length = types.length ∧ targets.length = types.length := by
  induction related with
  | nil => exact ⟨rfl, rfl⟩
  | cons _ _ ih => simpa only [List.length_cons, Nat.succ.injEq] using ih

theorem parseInput_correspondence {type : Core.Ty} {input : String} {expression : Core.Expr}
    (parsed : parseInput type input = .ok expression) :
    ∃ source target, InputRel type input source ∧ ValueRel type source target ∧
      ∀ environment store, Core.Evaluates environment store expression target store := by
  cases type <;> try simp [parseInput, fail] at parsed
  case word =>
    obtain ⟨value, wordParsed, returned⟩ := lower_bind_eq_ok.mp parsed
    cases returned
    exact ⟨.word value, .word value, .word (parseWord_some_of_ok wordParsed), .word value,
      fun _ _ => .word⟩
  case unit =>
    split at parsed
    · rename_i same
      subst input
      cases parsed
      exact ⟨.unit, .unit, .unit, .unit, fun _ _ => .unit⟩
    · contradiction
  case bool =>
    split at parsed
    · rename_i same
      subst input
      cases parsed
      exact ⟨.bool true, .bool true, .boolTrue, .bool true, fun _ _ => .bool⟩
    · split at parsed
      · rename_i same
        subst input
        cases parsed
        exact ⟨.bool false, .bool false, .boolFalse, .bool false, fun _ _ => .bool⟩
      · contradiction
  case sum left right =>
    cases left <;> cases right <;> simp only at parsed <;> try contradiction
    split at parsed
    · rename_i same
      subst input
      cases parsed
      exact ⟨.inr .unit, .inRight .unit .unit, .sumTrue, .inr .unit, fun _ _ => .inRight .unit⟩
    · split at parsed
      · rename_i same
        subst input
        cases parsed
        exact ⟨.inl .unit, .inLeft .unit .unit, .sumFalse, .inl .unit, fun _ _ => .inLeft .unit⟩
      · contradiction

/-- Actual arity checking and parsing provide all argument value and heap
premises needed by a function-preservation theorem. -/
theorem parseArguments_correspondence {parameters : List Core.Ty} {inputs : List String}
    {expression : Core.Expr} (parsed : parseArguments parameters inputs = .ok expression) :
    ∃ sources targets, InputsRel parameters inputs sources ∧ ValuesRel parameters sources targets ∧
      ∀ environment store, Core.Evaluates environment store expression (bundleValues targets) store := by
  induction parameters generalizing inputs expression with
  | nil =>
      cases inputs with
      | nil =>
          simp [parseArguments] at parsed
          cases parsed
          exact ⟨[], [], .nil, .nil, fun _ _ => .unit⟩
      | cons input inputs => simp [parseArguments, fail, Bind.bind, Except.bind] at parsed
  | cons type types ih =>
      cases inputs with
      | nil => simp [parseArguments, fail, Bind.bind, Except.bind] at parsed
      | cons input inputs =>
          by_cases length : inputs.length = types.length
          · cases types with
            | nil =>
                have empty : inputs = [] := List.eq_nil_of_length_eq_zero length
                subst inputs
                simp only [parseArguments, List.length_cons, List.length_nil, ↓reduceIte] at parsed
                obtain ⟨source, target, inputRelated, valueRelated, evaluated⟩ := parseInput_correspondence parsed
                exact ⟨[source], [target], .cons inputRelated .nil, .cons valueRelated .nil, evaluated⟩
            | cons next rest =>
                have lengths : (input :: inputs).length = (type :: next :: rest).length := congrArg Nat.succ length
                simp only [parseArguments, lengths, ↓reduceIte] at parsed
                obtain ⟨head, headParsed, tail⟩ := lower_bind_eq_ok.mp parsed
                obtain ⟨tail, tailParsed, returned⟩ := lower_bind_eq_ok.mp tail
                cases returned
                obtain ⟨source, target, inputRelated, valueRelated, headEvaluates⟩ := parseInput_correspondence headParsed
                obtain ⟨sources, targets, inputsRelated, valuesRelated, tailEvaluates⟩ := ih tailParsed
                refine ⟨source :: sources, target :: targets, .cons inputRelated inputsRelated,
                  .cons valueRelated valuesRelated, ?_⟩
                cases targets with
                | nil => have impossible := valuesRelated.length; simp at impossible
                | cons targetHead targets =>
                    intro environment store
                    exact .pair (headEvaluates environment store) (tailEvaluates environment store)
          · rw [parseArguments.eq_def] at parsed
            simp [length, fail, Bind.bind, Except.bind] at parsed

end Solcore.Frontend.RustHull.ScalarExecution
end

section
-- leanmerge: from Solcore.Frontend.RustHull.ExecutionCorrespondence
/-! Exact execution at the public scalar boundary. A semantic lowering proof
supplies a Core evaluation with its final value and store. These results connect
that evaluation to the actual public runner and any finite sequence of genuine
checkpoints, without identifying Hull meaning with a lowered Core program. -/
set_option autoImplicit false

namespace Solcore.Frontend.RustHull.ScalarExecution

/-- Successful preparation supplies the actual compiler and argument-parser
results, so downstream correspondence does not assume a second initialization. -/
theorem prepare_components {program : Program} {entry : String} {inputs : List String}
    {compilationFuel : Nat} {prepared : Prepared}
    (accepted : prepare program entry inputs compilationFuel = .ok prepared) :
    ∃ compiled argument,
      compile program entry compilationFuel = .ok compiled ∧
      parseArguments compiled.parameters inputs = .ok argument ∧
      prepared = ⟨compiled, argument⟩ := by
  cases compiled : compile program entry compilationFuel with
  | error error => simp [prepare, compiled, Except.mapError, Bind.bind, Except.bind] at accepted
  | ok function =>
      cases parsed : parseArguments function.parameters inputs with
      | error error => simp [prepare, compiled, parsed, Except.mapError, Bind.bind, Except.bind] at accepted
      | ok argument =>
          simp [prepare, compiled, parsed, Except.mapError, Bind.bind, Except.bind] at accepted
          cases accepted
          exact ⟨function, argument, rfl, parsed, rfl⟩

/-- The actual public preparation supplies its compiler result, independent
source arguments, their Core representation and unchanged initial heap. -/
theorem prepare_argument_correspondence {program : Program} {entry : String} {inputs : List String}
    {compilationFuel : Nat} {prepared : Prepared}
    (accepted : prepare program entry inputs compilationFuel = .ok prepared) :
    ∃ sources targets,
      compile program entry compilationFuel = .ok prepared.compiled ∧
      InputsRel prepared.compiled.parameters inputs sources ∧
      ValuesRel prepared.compiled.parameters sources targets ∧
      ∀ environment store, Core.Evaluates environment store prepared.argument (bundleValues targets) store := by
  obtain ⟨compiled, argument, checked, parsed, rfl⟩ := prepare_components accepted
  obtain ⟨sources, targets, inputsRelated, valuesRelated, evaluated⟩ := parseArguments_correspondence parsed
  exact ⟨sources, targets, checked, inputsRelated, valuesRelated, evaluated⟩

/-- A terminating semantic evaluation has one exact transition cost. Resuming
does not reset the heap or environment: every public chain completes with the
same value and store precisely when its combined fuel reaches that cost. -/
theorem evaluation_resumes_exact {prepared : Prepared} {value : Core.Value} {store : Core.Store}
    (evaluation : Core.Evaluates [] [] prepared.expression value store) :
    ∃ required, ∀ fuel additional last,
      Resumes (run prepared fuel) additional last →
        (last = .done value store ↔ required ≤ fuel + additional) ∧
        ((∃ checkpoint, last = .outOfFuel checkpoint) ↔ fuel + additional < required) := by
  obtain ⟨required, path⟩ := evaluation.toSteps
  refine ⟨required, ?_⟩
  intro fuel additional last resumed
  rw [resumed.eq_combined_run prepared fuel rfl]
  exact ⟨path.runStateful_done_iff, path.runStateful_outOfFuel_iff⟩

/-- The public runner returns the exact semantic value and final heap at every
sufficient budget, rather than merely returning some value of the right type. -/
theorem evaluation_run_complete {prepared : Prepared} {value : Core.Value} {store : Core.Store}
    (evaluation : Core.Evaluates [] [] prepared.expression value store) :
    ∃ required, ∀ fuel, required ≤ fuel → run prepared fuel = .done value store := by
  exact Core.evaluation_runStateful_complete_with_sufficient_fuel evaluation

/-- A genuine checkpoint after any finite chain retains enough information to
finish the semantic execution. The residual threshold uses all fuel consumed. -/
theorem evaluation_resumes_complete {prepared : Prepared} {value : Core.Value} {store : Core.Store}
    (evaluation : Core.Evaluates [] [] prepared.expression value store) :
    ∃ required, ∀ fuel additional last,
      Resumes (run prepared fuel) additional last →
      ∀ checkpoint, last = .outOfFuel checkpoint →
      ∀ more, required - (fuel + additional) ≤ more →
        resume checkpoint more = .done value store := by
  obtain ⟨required, exactCost⟩ := evaluation_resumes_exact evaluation
  refine ⟨required, ?_⟩
  intro fuel additional last resumed checkpoint exhausted more enough
  have cost := exactCost fuel (additional + more) (resume checkpoint more)
    (.step resumed exhausted more)
  exact cost.1.mpr (by omega)

/-- A completed public run has a semantic Core derivation for those exact
bytes/values and that exact heap; no replacement execution is introduced. -/
theorem run_done_evaluates {prepared : Prepared} {fuel : Nat}
    {value : Core.Value} {store : Core.Store}
    (completed : run prepared fuel = .done value store) :
    Core.Evaluates [] [] prepared.expression value store :=
  Core.runStateful_evaluation_sound completed

theorem resumes_done_evaluates {prepared : Prepared} {fuel additional : Nat}
    {last : Core.StatefulRunResult} {value : Core.Value} {store : Core.Store}
    (resumed : Resumes (run prepared fuel) additional last)
    (completed : last = .done value store) :
    Core.Evaluates [] [] prepared.expression value store :=
  run_done_evaluates ((resumed.eq_combined_run prepared fuel rfl).symm.trans completed)

end Solcore.Frontend.RustHull.ScalarExecution
end

section
-- leanmerge: from Solcore.Frontend.RustHull.LoweringStructure
/-! Decomposition of successful calls to the actual Hull compiler. Semantic
proofs use these results to recover the generated terms and the compiler's
annotation checks, rather than assuming a second translation agrees with it. -/
set_option autoImplicit false

namespace Solcore.Frontend.RustHull

theorem lowerExpression_pair_components {fuel : Nat} {signatures : List Signature}
    {scope : Scope} {type : Ty} {span : Option Span} {left right : Expr} {lowered : Lowered}
    (accepted : lowerExpression (fuel + 1) signatures scope
      ⟨type, .pair left right, span⟩ = .ok lowered) :
    ∃ leftCode rightCode,
      lowerExpression fuel signatures scope left = .ok leftCode ∧
      lowerExpression fuel signatures scope right = .ok rightCode ∧
      lowered = ⟨.product leftCode.type rightCode.type,
        Core.LocalSequence.pair leftCode.type rightCode.type
          leftCode.expression rightCode.expression⟩ := by
  simp only [lowerExpression] at accepted
  obtain ⟨_, _, accepted⟩ := lower_bind_eq_ok.mp accepted
  obtain ⟨leftCode, leftAccepted, accepted⟩ := lower_bind_eq_ok.mp accepted
  obtain ⟨rightCode, rightAccepted, accepted⟩ := lower_bind_eq_ok.mp accepted
  dsimp only [Bind.bind, Except.bind, Pure.pure] at accepted
  obtain ⟨checked, _, returned⟩ := lower_bind_eq_ok.mp accepted
  cases checked
  cases returned
  exact ⟨leftCode, rightCode, leftAccepted, rightAccepted, rfl⟩

theorem lowerExpression_projection_components {fuel : Nat} {signatures : List Signature}
    {scope : Scope} {type : Ty} {span : Option Span} {operand : Expr} {lowered : Lowered}
    (right : Bool)
    (accepted : lowerExpression (fuel + 1) signatures scope
      ⟨type, if right then .snd operand else .fst operand, span⟩ = .ok lowered) :
    ∃ value leftType rightType,
      lowerExpression fuel signatures scope operand = .ok value ∧
      value.type = .product leftType rightType ∧
      lowered = ⟨if right then rightType else leftType,
        Core.LanguageResult.bind (if right then rightType else leftType) value.expression
          (Core.LanguageResult.success
            (if right then .second (.var 0) else .first (.var 0)))⟩ := by
  cases right <;> simp only [Bool.false_eq_true, ↓reduceIte, lowerExpression] at accepted
  all_goals
    obtain ⟨_, _, accepted⟩ := lower_bind_eq_ok.mp accepted
    obtain ⟨value, valueAccepted, accepted⟩ := lower_bind_eq_ok.mp accepted
    cases shape : value.type <;> simp only [shape] at accepted
    all_goals try { simp [fail, lower_bind_eq_ok] at accepted }
    dsimp only [Bind.bind, Except.bind, Pure.pure] at accepted
    obtain ⟨checked, _, returned⟩ := lower_bind_eq_ok.mp accepted
    cases checked
    cases returned
    exact ⟨value, _, _, valueAccepted, shape, rfl⟩

theorem lowerExpression_injection_components {fuel : Nat} {signatures : List Signature}
    {scope : Scope} {type target : Ty} {span : Option Span} {operand : Expr} {lowered : Lowered}
    (right : Bool)
    (accepted : lowerExpression (fuel + 1) signatures scope
      ⟨type, if right then .inr target operand else .inl target operand, span⟩ = .ok lowered) :
    ∃ value leftType rightType,
      lowerType fuel target = .ok (.sum leftType rightType) ∧
      lowerExpression fuel signatures scope operand = .ok value ∧
      value.type = (if right then rightType else leftType) ∧
      lowered = ⟨.sum leftType rightType,
        Core.LanguageResult.bind (.sum leftType rightType) value.expression
          (Core.LanguageResult.success
            (if right then .inRight leftType (.var 0) else .inLeft rightType (.var 0)))⟩ := by
  cases right <;> simp only [Bool.false_eq_true, ↓reduceIte, lowerExpression] at accepted
  all_goals
    obtain ⟨_, _, accepted⟩ := lower_bind_eq_ok.mp accepted
    obtain ⟨targetType, targetAccepted, accepted⟩ := lower_bind_eq_ok.mp accepted
    obtain ⟨value, valueAccepted, accepted⟩ := lower_bind_eq_ok.mp accepted
    cases shape : targetType <;> simp only [shape] at accepted
    all_goals try { simp [fail, lower_bind_eq_ok] at accepted }
    dsimp only [Bind.bind, Except.bind, Pure.pure] at accepted
    obtain ⟨checked, matched, accepted⟩ := lower_bind_eq_ok.mp accepted
    cases checked
    have payload := expectType_eq_of_ok matched
    dsimp only [Bind.bind, Except.bind, Pure.pure] at accepted
    obtain ⟨checked, _, returned⟩ := lower_bind_eq_ok.mp accepted
    cases checked
    cases returned
    exact ⟨value, _, _, shape ▸ targetAccepted, valueAccepted, payload.symm, rfl⟩

theorem lowerExpression_conditional_components {fuel : Nat} {signatures : List Signature}
    {scope : Scope} {type target : Ty} {span : Option Span} {conditionExpr yes no : Expr} {lowered : Lowered}
    (accepted : lowerExpression (fuel + 1) signatures scope
      ⟨type, .ifThen target conditionExpr yes no, span⟩ = .ok lowered) :
    ∃ conditionCode test yesCode noCode,
      lowerExpression fuel signatures scope conditionExpr = .ok conditionCode ∧
      condition conditionCode = .ok test ∧
      lowerExpression fuel signatures scope yes = .ok yesCode ∧
      lowerExpression fuel signatures scope no = .ok noCode ∧
      yesCode.type = lowered.type ∧ noCode.type = lowered.type ∧
      lowered.expression = Core.LocalControl.choose lowered.type test yesCode.expression noCode.expression := by
  simp only [lowerExpression] at accepted
  obtain ⟨_, _, accepted⟩ := lower_bind_eq_ok.mp accepted
  obtain ⟨targetType, _, accepted⟩ := lower_bind_eq_ok.mp accepted
  obtain ⟨conditionCode, conditionAccepted, accepted⟩ := lower_bind_eq_ok.mp accepted
  obtain ⟨test, testAccepted, accepted⟩ := lower_bind_eq_ok.mp accepted
  obtain ⟨yesCode, yesAccepted, accepted⟩ := lower_bind_eq_ok.mp accepted
  obtain ⟨noCode, noAccepted, accepted⟩ := lower_bind_eq_ok.mp accepted
  obtain ⟨yesCheck, yesMatched, accepted⟩ := lower_bind_eq_ok.mp accepted
  cases yesCheck
  obtain ⟨noCheck, noMatched, accepted⟩ := lower_bind_eq_ok.mp accepted
  cases noCheck
  dsimp only [Bind.bind, Except.bind, Pure.pure] at accepted
  obtain ⟨checked, _, returned⟩ := lower_bind_eq_ok.mp accepted
  cases checked
  cases returned
  exact ⟨conditionCode, test, yesCode, noCode, conditionAccepted, testAccepted, yesAccepted,
    noAccepted, (expectType_eq_of_ok yesMatched).symm, (expectType_eq_of_ok noMatched).symm, rfl⟩

theorem lowerExpression_indexedInjection_components {fuel : Nat} {signatures : List Signature}
    {scope : Scope} {type target : Ty} {span : Option Span} {operand : Expr} {index : Nat}
    {lowered : Lowered}
    (accepted : lowerExpression (fuel + 1) signatures scope
      ⟨type, .inK index target operand, span⟩ = .ok lowered) :
    ∃ value targetType injected,
      lowerType fuel target = .ok targetType ∧
      lowerExpression fuel signatures scope operand = .ok value ∧
      inject index targetType value.type (.var 0) = .ok injected ∧
      lowered = ⟨targetType, Core.LanguageResult.bind targetType value.expression
        (Core.LanguageResult.success injected)⟩ := by
  simp only [lowerExpression] at accepted
  obtain ⟨_, _, accepted⟩ := lower_bind_eq_ok.mp accepted
  obtain ⟨targetType, targetAccepted, accepted⟩ := lower_bind_eq_ok.mp accepted
  obtain ⟨value, valueAccepted, accepted⟩ := lower_bind_eq_ok.mp accepted
  obtain ⟨injected, injectionAccepted, accepted⟩ := lower_bind_eq_ok.mp accepted
  dsimp only [Bind.bind, Except.bind, Pure.pure] at accepted
  obtain ⟨checked, _, returned⟩ := lower_bind_eq_ok.mp accepted
  cases checked
  cases returned
  exact ⟨value, targetType, injected, targetAccepted, valueAccepted, injectionAccepted, rfl⟩

end Solcore.Frontend.RustHull
end

section
-- leanmerge: from Solcore.Frontend.RustHull.ScopeCoverage
/-! The compiler cannot introduce an ordinary readable source name that is
absent from the source environment. Administrative names use the exact prefix
rejected by the Hull variable guard. This premise complements EnvironmentRel,
which relates values after the two lookups have succeeded. -/
set_option autoImplicit false

namespace Solcore.Frontend.RustHull.Correspondence

def ScopeCoverage (source : Semantics.Environment) (scope : Scope) : Prop :=
  ∀ name binding index,
    name.startsWith Effects.reservedPrefix = false →
    scope.lookup name = .ok (binding, index) →
    ∃ location, Semantics.lookupLocation source name = some location

theorem ScopeCoverage.empty (source : Semantics.Environment) : ScopeCoverage source [] := by
  intro name binding index _ looked
  simp [Scope.lookup, fail] at looked

theorem ScopeCoverage.temporary {source : Semantics.Environment} {scope : Scope}
    (covered : ScopeCoverage source scope) (type : Core.Ty) :
    ScopeCoverage source (scope.temporary type) := by
  intro name binding index allowed looked
  rw [Scope.temporary, scope_lookup_cons] at looked
  simp only [Option.none_beq_some, Bool.false_eq_true, ↓reduceIte] at looked
  cases old : scope.lookup name with
  | error error => simp only [old] at looked; contradiction
  | ok pair =>
      rcases pair with ⟨oldBinding, oldIndex⟩
      exact covered name oldBinding oldIndex allowed old

theorem ScopeCoverage.addLocal {source : Semantics.Environment} {scope : Scope}
    (covered : ScopeCoverage source scope) (name : String) (type : Core.Ty) (location : Nat) :
    ScopeCoverage ((name, location) :: source) (scope.addLocal name type) := by
  intro query binding index allowed looked
  by_cases same : name = query
  · subst query
    exact ⟨location, by simp [Semantics.lookupLocation]⟩
  · rw [Scope.addLocal, scope_lookup_cons] at looked
    simp only [Option.some_beq_some, beq_iff_eq, same, ↓reduceIte] at looked
    cases old : scope.lookup query with
    | error error => simp only [old] at looked; contradiction
    | ok pair =>
        rcases pair with ⟨oldBinding, oldIndex⟩
        obtain ⟨previous, found⟩ := covered query oldBinding oldIndex allowed old
        exact ⟨previous, by simpa [Semantics.lookupLocation, same] using found⟩

/-- Adding an administrative binding cannot create a new source variable:
the actual variable guard rejects its name before looking in the scope. -/
theorem ScopeCoverage.reserved {source : Semantics.Environment} {scope : Scope}
    (covered : ScopeCoverage source scope) (head : Binding)
    (reserved : ∀ name, head.name = some name → name.startsWith Effects.reservedPrefix = true) :
    ScopeCoverage source (head :: scope) := by
  intro name binding index allowed looked
  rw [scope_lookup_cons] at looked
  split at looked
  · rename_i named
    have forbidden := reserved name (beq_iff_eq.mp named)
    simp only [allowed] at forbidden
    contradiction
  · cases old : scope.lookup name with
    | error error => simp only [old] at looked; contradiction
    | ok pair =>
        rcases pair with ⟨oldBinding, oldIndex⟩
        exact covered name oldBinding oldIndex allowed old

theorem ScopeCoverage.of_reserved (source : Semantics.Environment) (scope : Scope)
    (reserved : ∀ binding ∈ scope, ∀ name, binding.name = some name →
      name.startsWith Effects.reservedPrefix = true) : ScopeCoverage source scope := by
  induction scope with
  | nil => exact .empty source
  | cons head rest ih =>
      apply ScopeCoverage.reserved
        (ih (fun binding member => reserved binding (List.mem_cons_of_mem head member))) head
      exact reserved head (List.mem_cons_self ..)

end Solcore.Frontend.RustHull.Correspondence
end
