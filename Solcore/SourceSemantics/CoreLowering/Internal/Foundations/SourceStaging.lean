import Solcore.SourceSemantics.CoreLowering.Internal.Foundations.ControlStatements
import Solcore.SourceSemantics.CoreLowering.Internal.Foundations.LiteralsAndStagedValues
import Solcore.Core.Correspondence
import Solcore.SourceSemantics.Dynamic.Evaluation
import Solcore.Resolved.LocalScope
import Solcore.SourceSemantics.CoreLowering.Internal.Foundations.LambdaViewsAndMarkedCaptures
import Solcore.Resolved.Typing
import Solcore.Resolved.Eval
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.RuntimeIndirectCalls
import Lean
import Solcore.Frontend.Internal.SpecializationProperties
import Solcore.Frontend.SourceSpecializationWorklist
import Solcore.SourceSemantics.Internal.Prepared.StatementReferences
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.LambdaViewTrees

/-!
# Source staging

The heap relation between Source and staged execution, staged integer meaning for declarations and residuals, reference origins and residual scope reachability.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SourceStagingHeapRelation
/-! Static bounds for every captured source location, including unused and
shadowed environment entries. These facts do not execute or rewrite code. -/

set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.SourceStagingHeapRelation
open Frontend SourceInference Solcore.SourceSemantics.Dynamic TypeSystem

set_option autoImplicit false
namespace Capture
open Solcore Solcore.Frontend Solcore.Frontend.SourceInference Solcore.SourceSemantics Solcore.SourceSemantics.Dynamic TypeSystem

/-- All positions count, including repeated identifiers and unused tails. -/
def EnvironmentBounded (bound : Nat) (environment : Dynamic.Environment) : Prop :=
  ∀ binding, binding ∈ environment → binding.2.index < bound

/-- A location stored anywhere in a value's nested closure captures. Mapping
keys and values, and every constructor payload, retain their original lists. -/
inductive ValueCaptures : Value → Location → Prop where
  | closure {function : Closure} {id : Resolved.LocalId} {location : Location}
      (member : (id, location) ∈ function.captured) :
      ValueCaptures (.closure function) location
  | productLeft {left right : Value} {location : Location}
      (inside : ValueCaptures left location) : ValueCaptures (.product left right) location
  | productRight {left right : Value} {location : Location}
      (inside : ValueCaptures right location) : ValueCaptures (.product left right) location
  | constructed {instantiation : DataConstructorInstantiation} {arguments : List Value}
      {value : Value} {location : Location} (member : value ∈ arguments)
      (inside : ValueCaptures value location) : ValueCaptures (.constructed instantiation arguments) location
  | mappingKey {keyType valueType : Ty} {entries : List (Value × Value)}
      {key value : Value} {location : Location} (member : (key, value) ∈ entries)
      (inside : ValueCaptures key location) : ValueCaptures (.mapping keyType valueType entries) location
  | mappingValue {keyType valueType : Ty} {entries : List (Value × Value)}
      {key value : Value} {location : Location} (member : (key, value) ∈ entries)
      (inside : ValueCaptures value location) : ValueCaptures (.mapping keyType valueType entries) location

def ValueBounded (bound : Nat) (value : Value) : Prop :=
  ∀ location, ValueCaptures value location → location.index < bound

def ValuesBounded (bound : Nat) (values : List Value) : Prop :=
  ∀ value, value ∈ values → ValueBounded bound value

def EntriesBounded (bound : Nat) (entries : List (Value × Value)) : Prop :=
  ∀ entry, entry ∈ entries → ValueBounded bound entry.1 ∧ ValueBounded bound entry.2

/-- Deep typing gives bounds for the entire environment, not only lookup hits. -/
theorem environment_bounded {heap : Heap} {scope : Resolved.LocalScope Scheme}
    {environment : Dynamic.Environment} (agrees : EnvironmentAgrees heap scope environment) :
    EnvironmentBounded heap.cells.length environment := by
  induction agrees with
  | nil => intro binding member; cases member
  | cons read _ _ _ tail =>
      intro binding member
      rcases List.mem_cons.mp member with same | rest
      · subst binding
        exact read.location_valid
      · exact tail binding rest

/-- One use of the original mutual typing recursor supplies all nested cases. -/
theorem value_bounded {context : SourceSemantics.Context} {heap : Heap} {value : Value} {type : Ty}
    (typed : ValueHasType context heap value type) : ValueBounded heap.cells.length value := by
  refine ValueHasType.rec
    (motive_1 := fun value _ _ => ValueBounded heap.cells.length value)
    (motive_2 := fun values _ _ => ValuesBounded heap.cells.length values)
    (motive_3 := fun entries _ _ _ => EntriesBounded heap.cells.length entries)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ typed
  · intro location captured; cases captured
  · intro _ location captured; cases captured
  · intro _ location captured; cases captured
  · intro _ location captured; cases captured
  · intro _ _ _ location captured; cases captured
  · intro left right leftType rightType leftTyped rightTyped leftBound rightBound location captured
    cases captured with
    | productLeft inside => exact leftBound location inside
    | productRight inside => exact rightBound location inside
  · intro _ location captured; cases captured
  · intro instantiation values valid typedValues bounded location captured
    cases captured with
    | constructed member inside => exact bounded _ member location inside
  · intro keyType valueType entries typedEntries bounded location captured
    cases captured with
    | mappingKey member inside => exact (bounded _ member).1 location inside
    | mappingValue member inside => exact (bounded _ member).2 location inside
  · intro function signatures code evidence agrees location captured
    cases captured with
    | closure member => exact environment_bounded agrees _ member
  · intro function valid evidence location captured; cases captured
  · intro function location captured; cases captured
  · intro value inner typedValue bounded; exact bounded
  · intro value member; cases member
  · intro value values type types typedHead typedTail headBound tailBound candidate member
    rcases List.mem_cons.mp member with same | rest
    · subst candidate; exact headBound
    · exact tailBound candidate rest
  · intro keyType valueType entry member; cases member
  · intro key value entries keyType valueType keyTyped valueTyped entriesTyped keyBound valueBound tailBound entry member
    rcases List.mem_cons.mp member with same | rest
    · subst entry; exact ⟨keyBound, valueBound⟩
    · exact tailBound entry rest

/-- Ordered payloads use the same value theorem; no second value induction. -/
theorem values_bounded {context : SourceSemantics.Context} {heap : Heap} {values : List Value} {types : List Ty}
    (typed : ValuesHaveTypes context heap values types) : ValuesBounded heap.cells.length values := by
  induction values generalizing types with
  | nil => intro value member; cases member
  | cons headValue tailValues ih =>
      cases typed with
      | cons head tail =>
          intro value member
          rcases List.mem_cons.mp member with same | rest
          · subst value; exact value_bounded head
          · exact ih tail value rest

theorem entries_bounded {context : SourceSemantics.Context} {heap : Heap} {entries : List (Value × Value)}
    {keyType valueType : Ty} (typed : MappingEntriesHaveTypes context heap entries keyType valueType) :
    EntriesBounded heap.cells.length entries := by
  induction entries with
  | nil => intro entry member; cases member
  | cons headEntry tailEntries ih =>
      cases typed with
      | cons key value tail =>
          intro entry member
          rcases List.mem_cons.mp member with same | rest
          · subst entry; exact ⟨value_bounded key, value_bounded value⟩
          · exact ih tail entry rest

theorem generalized_bounded {context : SourceSemantics.Context} {heap : Heap} {function : GeneralizedClosure}
    (typed : GeneralizedClosureWellTyped context heap function) :
    EnvironmentBounded heap.cells.length function.captured :=
  environment_bounded typed.captures

/-- Both optional fields are inspected independently, without assuming an
ordinary cell or erasing its generalized descriptor. -/
inductive CellCaptures (cell : Cell) : Location → Prop where
  | value {payload : Value} {location : Location} (present : cell.value = some payload)
      (inside : ValueCaptures payload location) : CellCaptures cell location
  | generalized {function : GeneralizedClosure} {id : Resolved.LocalId} {location : Location}
      (present : cell.generalized = some function) (member : (id, location) ∈ function.captured) :
      CellCaptures cell location

def HeapCaptures (heap : Heap) (location : Location) : Prop :=
  ∃ cell, cell ∈ heap.cells ∧ CellCaptures cell location

theorem cell_bounded {context : SourceSemantics.Context} {heap : Heap} {cell : Cell}
    (typed : CellWellTyped context heap cell) {location : Location}
    (captured : CellCaptures cell location) : location.index < heap.cells.length := by
  cases captured with
  | value present inside =>
      have typedValue := typed.value
      rw [present] at typedValue
      cases typedValue with
      | some valueTyped => exact value_bounded valueTyped location inside
  | generalized present member =>
      exact generalized_bounded (typed.generalized_inv present).2 _ member

theorem heap_bounded {context : SourceSemantics.Context} {heap : Heap} (typed : HeapWellTyped context heap)
    {location : Location} (captured : HeapCaptures heap location) : location.index < heap.cells.length := by
  obtain ⟨cell, member, inside⟩ := captured
  exact cell_bounded (typed cell member) inside

/-- A future suffix address cannot already occur in a typed initial heap. -/
theorem heap_excludes_future {context : SourceSemantics.Context} {before : Heap} (typed : HeapWellTyped context before)
    {location : Location} (future : before.cells.length ≤ location.index) :
    ¬ HeapCaptures before location := by
  intro captured
  exact Nat.not_lt_of_ge future (heap_bounded typed captured)

/-- Bounds concern every old capture, with no promise about a future suffix's
values or about the execution of any closure body. -/
theorem heap_excludes_suffix_index {context : SourceSemantics.Context} {before : Heap}
    (typed : HeapWellTyped context before) (offset : Nat) :
    ¬ HeapCaptures before ⟨before.cells.length + offset⟩ :=
  heap_excludes_future typed (Nat.le_add_right _ _)

/-- Shadowing does not discard the older capture from the boundedness fact. -/
theorem shadowed_capture {heap : Heap} {scope : Resolved.LocalScope Scheme}
    {id : Resolved.LocalId} {first second : Location} {tail : Dynamic.Environment}
    (agrees : EnvironmentAgrees heap scope ((id, first) :: (id, second) :: tail)) :
    first.index < heap.cells.length ∧ second.index < heap.cells.length := by
  have bounded := environment_bounded agrees
  exact ⟨bounded (id, first) (by simp), bounded (id, second) (by simp)⟩

theorem future_closure_not_typed {context : SourceSemantics.Context} {heap : Heap} {function : Closure}
    {id : Resolved.LocalId} {location : Location} {type : Ty}
    (member : (id, location) ∈ function.captured) (future : heap.cells.length ≤ location.index) :
    ¬ ValueHasType context heap (.closure function) type := by
  intro typed
  exact Nat.not_lt_of_ge future (value_bounded typed location (.closure member))

end Capture

/-- One entry per original cell. Retained cells have one residual address. -/
abbrev LocationMap := List (Option Dynamic.Location)
def Maps (mapping : LocationMap) (source residual : Dynamic.Location) : Prop :=
  mapping[source.index]? = some (some residual)
def Extends (before after : LocationMap) : Prop :=
  ∀ source residual, Maps before source residual → Maps after source residual

/-- The retained addresses enumerate the complete residual heap in order. -/
inductive Ordered : LocationMap → Nat → Prop where
  | nil : Ordered [] 0
  | keep {mapping : LocationMap} {length : Nat} (prior : Ordered mapping length) :
      Ordered (mapping ++ [some ⟨length⟩]) (length + 1)
  | drop {mapping : LocationMap} {length : Nat} (prior : Ordered mapping length) :
      Ordered (mapping ++ [none]) length

namespace Maps
 theorem bound {mapping : LocationMap} {source residual : Dynamic.Location}
    (mapped : Maps mapping source residual) : source.index < mapping.length :=
  (List.getElem?_eq_some_iff.mp mapped).1
 theorem functional {mapping : LocationMap} {source left right : Dynamic.Location}
    (a : Maps mapping source left) (b : Maps mapping source right) : left = right := by
  exact Option.some.inj (Option.some.inj (a.symm.trans b))
end Maps

theorem extends_append (mapping suffix : LocationMap) : Extends mapping (mapping ++ suffix) := by
  intro source residual mapped
  simpa only [Maps, List.getElem?_append_left mapped.bound] using mapped

theorem Extends.trans {first middle last : LocationMap} (left : Extends first middle)
    (right : Extends middle last) : Extends first last := fun _ _ mapped => right _ _ (left _ _ mapped)

def identityMap (length : Nat) : LocationMap := (List.range length).map (fun n => some ⟨n⟩)

theorem identity_ordered (length : Nat) : Ordered (identityMap length) length := by
  induction length with
  | zero => exact .nil
  | succ n ih => simpa only [identityMap, List.range_succ, List.map_append, List.map_cons, List.map_nil] using Ordered.keep ih

theorem identity_maps {length : Nat} {source : Dynamic.Location} (bound : source.index < length) :
    Maps (identityMap length) source source := by
  simp [Maps, identityMap, bound]

inductive EnvironmentRel (mapping : LocationMap) : Dynamic.Environment → Dynamic.Environment → Prop where
  | nil : EnvironmentRel mapping [] []
  | cons {id : Resolved.LocalId} {source target : Dynamic.Location}
      {left right : Dynamic.Environment} (location : Maps mapping source target)
      (tail : EnvironmentRel mapping left right) :
      EnvironmentRel mapping ((id, source) :: left) ((id, target) :: right)

namespace EnvironmentRel
 theorem mono {a b : LocationMap} (extension : Extends a b) {left right : Dynamic.Environment}
    (related : EnvironmentRel a left right) : EnvironmentRel b left right := by
  induction related with
  | nil => exact .nil
  | cons location tail ih => exact .cons (extension _ _ location) ih
 theorem identity {length : Nat} {environment : Dynamic.Environment}
    (bounded : Capture.EnvironmentBounded length environment) : EnvironmentRel (identityMap length) environment environment := by
  induction environment with
  | nil => exact .nil
  | cons binding tail ih =>
      exact .cons (identity_maps (bounded _ (by simp))) (ih (fun row member => bounded row (by simp [member])))
 theorem length {mapping : LocationMap} {left right : Dynamic.Environment} (related : EnvironmentRel mapping left right) : left.length = right.length := by
  induction related with
  | nil => rfl
  | cons _ _ ih => exact congrArg Nat.succ ih
end EnvironmentRel

mutual
 inductive ValueRel (mapping : LocationMap) : Dynamic.Value → Dynamic.Value → Prop where
  | unit : ValueRel mapping .unit .unit
  | bool (v : Bool) : ValueRel mapping (.bool v) (.bool v)
  | word (v : Core.Word) : ValueRel mapping (.word v) (.word v)
  | integer (v : Int) : ValueRel mapping (.integer v) (.integer v)
  | proxy (type : TypeSystem.Ty) : ValueRel mapping (.proxy type) (.proxy type)
  | product {a b c d : Dynamic.Value} (left : ValueRel mapping a c) (right : ValueRel mapping b d) :
      ValueRel mapping (.product a b) (.product c d)
  | constructed {instantiation : DataConstructorInstantiation} {left right : List Dynamic.Value}
      (values : ValuesRel mapping left right) : ValueRel mapping (.constructed instantiation left) (.constructed instantiation right)
  | mapping {keyType valueType : TypeSystem.Ty} {left right : List (Dynamic.Value × Dynamic.Value)}
      (entries : EntriesRel mapping left right) : ValueRel mapping (.mapping keyType valueType left) (.mapping keyType valueType right)
  | closure {function : Dynamic.Closure} {captured : Dynamic.Environment}
      (captures : EnvironmentRel mapping function.captured captured) :
      ValueRel mapping (.closure function) (.closure { function with captured := captured })
  | global (function : Dynamic.GlobalFunction) : ValueRel mapping (.global function) (.global function)
  | builtin (function : Dynamic.BuiltinFunction) : ValueRel mapping (.builtin function) (.builtin function)
 inductive ValuesRel (mapping : LocationMap) : List Dynamic.Value → List Dynamic.Value → Prop where
  | nil : ValuesRel mapping [] []
  | cons {a b : Dynamic.Value} {left right : List Dynamic.Value}
      (head : ValueRel mapping a b) (tail : ValuesRel mapping left right) : ValuesRel mapping (a :: left) (b :: right)
 inductive EntriesRel (mapping : LocationMap) : List (Dynamic.Value × Dynamic.Value) → List (Dynamic.Value × Dynamic.Value) → Prop where
  | nil : EntriesRel mapping [] []
  | cons {a b c d : Dynamic.Value} {left right : List (Dynamic.Value × Dynamic.Value)}
      (key : ValueRel mapping a c) (value : ValueRel mapping b d) (tail : EntriesRel mapping left right) :
      EntriesRel mapping ((a,b) :: left) ((c,d) :: right)
end

theorem ValueRel.mono {a b : LocationMap} (extension : Extends a b) {left right : Dynamic.Value}
    (related : ValueRel a left right) : ValueRel b left right := by
  refine ValueRel.rec
    (motive_1 := fun left right _ => ValueRel b left right)
    (motive_2 := fun left right _ => ValuesRel b left right)
    (motive_3 := fun left right _ => EntriesRel b left right)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ related
  · exact .unit
  · exact fun v => .bool v
  · exact fun v => .word v
  · exact fun v => .integer v
  · exact fun t => .proxy t
  · intros; exact .product ‹ValueRel b _ _› ‹ValueRel b _ _›
  · intros; exact .constructed ‹ValuesRel b _ _›
  · intros; exact .mapping ‹EntriesRel b _ _›
  · intro function captured captures; exact .closure (captures.mono extension)
  · exact fun f => .global f
  · exact fun f => .builtin f
  · exact .nil
  · intros; exact .cons ‹ValueRel b _ _› ‹ValuesRel b _ _›
  · exact .nil
  · intros; exact .cons ‹ValueRel b _ _› ‹ValueRel b _ _› ‹EntriesRel b _ _›

/-- Structural identity uses the independently established bounds, without
another induction on source typing or any closure-body law. -/
theorem value_identity {length : Nat} (value : Dynamic.Value)
    (bounded : Capture.ValueBounded length value) : ValueRel (identityMap length) value value := by
  apply Dynamic.Value.rec
    (motive_1 := fun v => Capture.ValueBounded length v → ValueRel (identityMap length) v v)
    (motive_2 := fun values => Capture.ValuesBounded length values → ValuesRel (identityMap length) values values)
    (motive_3 := fun entries => Capture.EntriesBounded length entries → EntriesRel (identityMap length) entries entries)
    (motive_4 := fun pair => Capture.ValueBounded length pair.1 ∧ Capture.ValueBounded length pair.2 →
      ValueRel (identityMap length) pair.1 pair.1 ∧ ValueRel (identityMap length) pair.2 pair.2)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ value bounded
  · intro _; exact .unit
  · intro v _; exact .bool v
  · intro v _; exact .word v
  · intro v _; exact .integer v
  · intro left right li ri bound
    exact .product (li (fun location found => bound location (.productLeft found)))
      (ri (fun location found => bound location (.productRight found)))
  · intro t _; exact .proxy t
  · intro inst values ih bound
    exact .constructed (ih (fun value member location found => bound location (.constructed member found)))
  · intro kt vt entries ih bound
    exact .mapping (ih (fun pair member => ⟨fun location found => bound location (.mappingKey member found),
      fun location found => bound location (.mappingValue member found)⟩))
  · intro function bound
    have captured : EnvironmentRel (identityMap length) function.captured function.captured :=
      EnvironmentRel.identity (fun binding member => bound binding.2 (.closure member))
    simpa only using ValueRel.closure captured
  · intro f _; exact .global f
  · intro f _; exact .builtin f
  · intro _; exact .nil
  · intro head tail hi ti bound
    exact .cons (hi (bound head (by simp))) (ti (fun v member => bound v (by simp [member])))
  · intro _; exact .nil
  · intro pair tail pi ti bound
    exact .cons (pi (bound pair (by simp))).1 (pi (bound pair (by simp))).2
      (ti (fun pair member => bound pair (by simp [member])))
  · intro first second fi si bound; exact ⟨fi bound.1, si bound.2⟩

inductive GeneralizedRel (mapping : LocationMap) : Dynamic.GeneralizedClosure → Dynamic.GeneralizedClosure → Prop where
  | captures {function : Dynamic.GeneralizedClosure} {captured : Dynamic.Environment}
      (related : EnvironmentRel mapping function.captured captured) :
      GeneralizedRel mapping function {function with captured := captured}

inductive OptionalRel {α : Type} (relation : α → α → Prop) : Option α → Option α → Prop where
  | none : OptionalRel relation none none
  | some {left right : α} (related : relation left right) : OptionalRel relation (some left) (some right)

structure CellRel (mapping : LocationMap) (source residual : Dynamic.Cell) : Prop where
  type : source.type = residual.type
  value : OptionalRel (ValueRel mapping) source.value residual.value
  generalized : OptionalRel (GeneralizedRel mapping) source.generalized residual.generalized

theorem OptionalRel.mono {α : Type} {R S : α → α → Prop} (change : ∀ a b, R a b → S a b)
    {left right : Option α} (related : OptionalRel R left right) : OptionalRel S left right := by
  cases related with
  | none => exact .none
  | some value => exact .some (change _ _ value)

theorem GeneralizedRel.mono {a b : LocationMap} (extension : Extends a b)
    {left right : Dynamic.GeneralizedClosure} (related : GeneralizedRel a left right) : GeneralizedRel b left right := by
  cases related with
  | captures captures => exact .captures (captures.mono extension)

theorem CellRel.mono {a b : LocationMap} (extension : Extends a b) {left right : Dynamic.Cell}
    (related : CellRel a left right) : CellRel b left right :=
  ⟨related.type, related.value.mono (fun _ _ value => value.mono extension),
    related.generalized.mono (fun _ _ value => value.mono extension)⟩

theorem cell_identity {context : SourceSemantics.Context} {heap : Dynamic.Heap} {cell : Dynamic.Cell}
    (typed : Dynamic.CellWellTyped context heap cell) : CellRel (identityMap heap.cells.length) cell cell := by
  refine ⟨rfl, ?_, ?_⟩
  · cases present : cell.value with
    | none => exact .none
    | some value =>
        have valueTyped := typed.value
        rw [present] at valueTyped
        cases valueTyped with
        | some valueTyped => exact .some (value_identity value (Capture.value_bounded valueTyped))
  · cases present : cell.generalized with
    | none => exact .none
    | some function =>
        have captured := EnvironmentRel.identity (Capture.generalized_bounded (typed.generalized_inv present).2)
        exact .some (by simpa only using GeneralizedRel.captures captured)

abbrev integerCell := SourceStagedIntegerStatementsMeaning.integerCell
/-- Eligibility is cell shape, not a claim that a compiler erased the cell. -/
def EligibleDrop (cell : Dynamic.Cell) : Prop := ∃ value, cell = integerCell value

/-- Every original cell is accounted for; the residual heap is complete. A
separate actual evaluator/pass receipt must justify which eligible cells a
consumer omits. This structure is not an execution theorem. -/
structure HeapRel (mapping : LocationMap) (source residual : Dynamic.Heap) : Prop where
  length : mapping.length = source.cells.length
  ordered : Ordered mapping residual.cells.length
  kept : ∀ (index : Nat) (target : Dynamic.Location) (cell : Dynamic.Cell), mapping[index]? = some (some target) → source.cells[index]? = some cell →
    ∃ residualCell, residual.cells[target.index]? = some residualCell ∧ CellRel mapping cell residualCell
  dropped : ∀ (index : Nat), mapping[index]? = some none →
    ∃ cell, source.cells[index]? = some cell ∧ EligibleDrop cell

theorem HeapRel.identity {context : SourceSemantics.Context} {heap : Dynamic.Heap}
    (typed : Dynamic.HeapWellTyped context heap) : HeapRel (identityMap heap.cells.length) heap heap := by
  refine ⟨by simp [identityMap], identity_ordered _, ?_, ?_⟩
  · intro index target cell mapped selected
    have bound : index < heap.cells.length := by
      have h := (List.getElem?_eq_some_iff.mp mapped).1
      simpa only [identityMap, List.length_map, List.length_range] using h
    have same := Maps.functional mapped (identity_maps (source := ⟨index⟩) bound)
    subst target
    exact ⟨cell, selected, cell_identity (typed cell (List.mem_of_getElem? selected))⟩
  · intro index missing
    have bound : index < heap.cells.length := by
      have h := (List.getElem?_eq_some_iff.mp missing).1
      simpa only [identityMap, List.length_map, List.length_range] using h
    have mappedSelf := identity_maps (source := ⟨index⟩) bound
    rw [show (identityMap heap.cells.length)[index]? = some (some (⟨index⟩ : Dynamic.Location)) from mappedSelf] at missing
    cases missing

private theorem slot_append {α : Type} {list : List α} {last slot : α} {index : Nat}
    (found : (list ++ [last])[index]? = some slot) :
    list[index]? = some slot ∨ index = list.length ∧ slot = last := by
  by_cases before : index < list.length
  · exact .inl (by simpa only [List.getElem?_append_left before] using found)
  · have bound := (List.getElem?_eq_some_iff.mp found).1
    have same : index = list.length := by simp only [List.length_append, List.length_singleton] at bound; omega
    subst index
    have eq : last = slot := Option.some.inj (List.getElem?_concat_length.symm.trans found)
    exact .inr ⟨rfl, eq.symm⟩

theorem Ordered.target_bound {mapping : LocationMap} {length : Nat} (ordered : Ordered mapping length)
    {source residual : Dynamic.Location} (mapped : Maps mapping source residual) : residual.index < length := by
  induction ordered with
  | nil => simp [Maps] at mapped
  | keep prior ih =>
      rcases slot_append mapped with old | ⟨_, same⟩
      · exact Nat.lt_succ_of_lt (ih old)
      · cases Option.some.inj same
        exact Nat.lt_succ_self _
  | drop prior ih =>
      rcases slot_append mapped with old | ⟨_, same⟩
      · exact ih old
      · cases same

/-- No two retained source cells share a target; aliases of one source cell
still share exactly the same target through Maps.functional. -/
theorem Ordered.injective {mapping : LocationMap} {length : Nat} (ordered : Ordered mapping length)
    {left right target : Dynamic.Location} (a : Maps mapping left target) (b : Maps mapping right target) : left = right := by
  induction ordered with
  | nil => simp [Maps] at a
  | keep prior ih =>
      rcases slot_append a with oldA | ⟨lastA, targetA⟩ <;>
        rcases slot_append b with oldB | ⟨lastB, targetB⟩
      · exact ih oldA oldB
      · have bound := prior.target_bound oldA
        cases Option.some.inj targetB
        exact False.elim (Nat.lt_irrefl _ bound)
      · have bound := prior.target_bound oldB
        cases Option.some.inj targetA
        exact False.elim (Nat.lt_irrefl _ bound)
      · cases left; cases right; congr; exact lastA.trans lastB.symm
  | drop prior ih =>
      rcases slot_append a with oldA | ⟨_, impossible⟩
      · rcases slot_append b with oldB | ⟨_, impossible⟩
        · exact ih oldA oldB
        · cases impossible
      · cases impossible

/-- Append one retained cell, shifting its residual address past only retained
predecessors. Full old values and captures are transported by map extension. -/
theorem HeapRel.keep {mapping : LocationMap} {source residual : Dynamic.Heap}
    (related : HeapRel mapping source residual) {sourceCell residualCell : Dynamic.Cell}
    (cell : CellRel mapping sourceCell residualCell) :
    HeapRel (mapping ++ [some ⟨residual.cells.length⟩])
      ⟨source.cells ++ [sourceCell]⟩ ⟨residual.cells ++ [residualCell]⟩ := by
  refine ⟨by simp only [List.length_append, List.length_singleton, related.length], ?_, ?_, ?_⟩
  · simpa only [List.length_append, List.length_singleton] using Ordered.keep related.ordered
  · intro index target selected mapped read
    rcases slot_append mapped with old | ⟨last, targetEq⟩
    · have bound : index < source.cells.length := by
        rw [← related.length]; exact (List.getElem?_eq_some_iff.mp old).1
      obtain ⟨output, found, repr⟩ := related.kept index target selected old
        (by simpa only [List.getElem?_append_left bound] using read)
      refine ⟨output, ?_, repr.mono (extends_append _ _)⟩
      simpa only [List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1] using found
    · cases Option.some.inj targetEq
      have sourceIndex : index = source.cells.length := last.trans related.length
      have selectedEq : selected = sourceCell := by
        rw [sourceIndex, List.getElem?_concat_length] at read
        exact (Option.some.inj read).symm
      subst selected
      exact ⟨residualCell, List.getElem?_concat_length, cell.mono (extends_append _ _)⟩
  · intro index absent
    rcases slot_append absent with old | ⟨_, impossible⟩
    · obtain ⟨cell, found, eligible⟩ := related.dropped index old
      exact ⟨cell, by simpa only [List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1] using found, eligible⟩
    · cases impossible

/-- Omit only one ordinary initialized Integer cell; no existing cell or
residual allocation is discarded. This is a structural extension helper. -/
theorem HeapRel.erase_integer {mapping : LocationMap} {source residual : Dynamic.Heap}
    (related : HeapRel mapping source residual) (value : Int) :
    HeapRel (mapping ++ [none]) ⟨source.cells ++ [integerCell value]⟩ residual := by
  refine ⟨by simp only [List.length_append, List.length_singleton, related.length], Ordered.drop related.ordered, ?_, ?_⟩
  · intro index target selected mapped read
    rcases slot_append mapped with old | ⟨_, impossible⟩
    · have bound : index < source.cells.length := by
        rw [← related.length]; exact (List.getElem?_eq_some_iff.mp old).1
      obtain ⟨output, found, repr⟩ := related.kept index target selected old
        (by simpa only [List.getElem?_append_left bound] using read)
      exact ⟨output, found, repr.mono (extends_append _ _)⟩
    · cases impossible
  · intro index absent
    rcases slot_append absent with old | ⟨last, _⟩
    · obtain ⟨cell, found, eligible⟩ := related.dropped index old
      exact ⟨cell, by simpa only [List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1] using found, eligible⟩
    · refine ⟨integerCell value, ?_, value, rfl⟩
      rw [last, related.length]
      exact List.getElem?_concat_length

theorem HeapRel.erase_allocated {mapping : LocationMap} {source residual after : Dynamic.Heap}
    (related : HeapRel mapping source residual) {value : Int} {location : Dynamic.Location}
    (allocated : Dynamic.Heap.Allocates source .integer (some (.integer value)) location after) :
    HeapRel (mapping ++ [none]) after residual := by
  cases allocated
  exact related.erase_integer value

theorem HeapRel.keep_allocated {mapping : LocationMap} {source residual afterSource afterResidual : Dynamic.Heap}
    (related : HeapRel mapping source residual) {type : TypeSystem.Ty} {left right : Dynamic.Value}
    {sourceLocation residualLocation : Dynamic.Location} (value : ValueRel mapping left right)
    (sourceAllocation : Dynamic.Heap.Allocates source type (some left) sourceLocation afterSource)
    (residualAllocation : Dynamic.Heap.Allocates residual type (some right) residualLocation afterResidual) :
    HeapRel (mapping ++ [some residualLocation]) afterSource afterResidual := by
  cases sourceAllocation
  cases residualAllocation
  exact related.keep ⟨rfl, .some value, .none⟩

/-- Repeated structural omission preserves the order and all retained cells. -/
theorem HeapRel.erase_suffix {mapping : LocationMap} {source residual : Dynamic.Heap}
    (related : HeapRel mapping source residual) (values : List Int) :
    HeapRel (mapping ++ List.replicate values.length none)
      ⟨source.cells ++ values.map integerCell⟩ residual := by
  induction values generalizing mapping source with
  | nil => simpa using related
  | cons head tail ih =>
      simpa [List.replicate_succ, List.append_assoc] using ih (related.erase_integer head)

/-- Every retained initial location keeps its original physical index. -/
def IdentityPrefix (mapping : LocationMap) (length : Nat) : Prop :=
  ∀ location : Dynamic.Location, location.index < length → Maps mapping location location

theorem identity_prefix (length : Nat) : IdentityPrefix (identityMap length) length :=
  fun _location bound => identity_maps bound

theorem IdentityPrefix.extend {mapping after : LocationMap} {length : Nat}
    (same : IdentityPrefix mapping length) (extension : Extends mapping after) :
    IdentityPrefix after length := fun location bound => extension _ _ (same location bound)

/-- The old full heap is the residual heap. Original captured locations remain
valid because deep source typing bounded every location before the suffix existed. -/
theorem erase_typed_suffix {context : SourceSemantics.Context} {before after : Dynamic.Heap}
    (typed : HeapWellTyped context before) (values : List Int)
    (cells : after.cells = before.cells ++ values.map integerCell) :
    HeapRel (identityMap before.cells.length ++ List.replicate values.length none) after before ∧
    IdentityPrefix (identityMap before.cells.length ++ List.replicate values.length none) before.cells.length := by
  have heapEq : after = ⟨before.cells ++ values.map integerCell⟩ := by cases after; cases cells; rfl
  subst after
  exact ⟨(HeapRel.identity typed).erase_suffix values,
    (identity_prefix _).extend (extends_append _ _)⟩

/-- A discarded cell is always ordinary, initialized, and scalar. -/
theorem EligibleDrop.fields {cell : Dynamic.Cell} (eligible : EligibleDrop cell) :
    cell.type = .integer ∧ cell.generalized = none ∧ ∃ value, cell.value = some (.integer value) := by
  obtain ⟨value, rfl⟩ := eligible
  exact ⟨rfl, rfl, value, rfl⟩

/-- A generalized cell is never an eligible omission, even if its declared type
is Integer or it also contains an ordinary value. -/
theorem generalized_not_eligible {cell : Dynamic.Cell} {closure : Dynamic.GeneralizedClosure}
    (present : cell.generalized = some closure) : ¬ EligibleDrop cell := by
  intro eligible
  rw [eligible.fields.2.1] at present
  cases present

/-- Every occurrence in a captured environment must still have a mapped target;
shadowed bindings and unused tails receive the same check. -/
theorem EnvironmentRel.member {mapping : LocationMap} {source residual : Dynamic.Environment}
    (related : EnvironmentRel mapping source residual) {id : Resolved.LocalId} {location : Dynamic.Location}
    (member : (id, location) ∈ source) :
    ∃ target, (id, target) ∈ residual ∧ Maps mapping location target := by
  induction related with
  | nil => cases member
  | cons mapped tail ih =>
      rcases List.mem_cons.mp member with same | rest
      · cases same
        exact ⟨_, by simp, mapped⟩
      · obtain ⟨target, found, mapped⟩ := ih rest
        exact ⟨target, List.mem_cons_of_mem _ found, mapped⟩

theorem EnvironmentRel.not_dropped {mapping : LocationMap} {source residual : Dynamic.Environment}
    (related : EnvironmentRel mapping source residual) {id : Resolved.LocalId} {location : Dynamic.Location}
    (member : (id, location) ∈ source) : mapping[location.index]? ≠ some none := by
  obtain ⟨target, _, mapped⟩ := related.member member
  unfold Maps at mapped
  rw [mapped]
  simp

/-- The actual accepted Integer evaluator supplies the ordered inputs, selected
let cells and source trace. This exposes a permissible suffix relation; it does
not assert that a residual compiler has chosen to omit the whole call. -/
theorem integer_function_suffix
    {function : SourceInference.CheckedFunction} {arguments : List Int} {value : Int}
    {program : SourceSemantics.Program} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {before : Dynamic.Heap} {facts : BodyFacts}
    (accepted : Frontend.SourceCoreElaboration.evaluateStagedIntegerFunction function arguments = .ok value)
    (unique : NodeOccurrencesUnique function.typedBody)
    (typed : BodyHasType function.typedBody context .integer facts)
    (ledger : context.solvedRequirements = function.solvedRequirements)
    (valid : SourceStagedClosedEvaluationMeaning.UsedValid context function.solvedRequirements
      (function.solvedRequirements.map (·.id)))
    (initial : HeapWellTyped context before) :
    Frontend.SourceCoreElaboration.Internal.Staged.Statements.FunctionChecked function arguments value ∧
    ∃ environment bound roots final after added,
      roots.map NodeId.statement = function.typedBody.roots ∧
      Dynamic.BindersAllocate [] before function.typedBody.inputs
        (arguments.map Dynamic.Value.integer) environment bound ∧
      Dynamic.StatementsExecute program context evidence function.typedBody environment bound roots final
        (.returned (.integer value)) after ∧
      SourceStagedIntegerStatementsMeaning.Extends before after (arguments ++ added) ∧
      HeapRel (identityMap before.cells.length ++ List.replicate (arguments ++ added).length none) after before ∧
      IdentityPrefix (identityMap before.cells.length ++ List.replicate (arguments ++ added).length none) before.cells.length ∧
      ValueRel (identityMap before.cells.length ++ List.replicate (arguments ++ added).length none)
        (.integer value) (.integer value) := by
  obtain ⟨checked, environment, bound, roots, final, after, added, rootsEq, allocated, executed, cells⟩ :=
    SourceStagedIntegerStatementsMeaning.evaluateStagedIntegerFunction_sound
      (program := program) (evidence := evidence) (before := before)
      accepted unique typed ledger valid
  obtain ⟨related, initialPrefix⟩ := erase_typed_suffix initial (arguments ++ added) cells
  exact ⟨checked, environment, bound, roots, final, after, added, rootsEq, allocated, executed,
    cells, related, initialPrefix, .integer value⟩

/-- First-match lookup is preserved together with all shadowed list entries. -/
theorem EnvironmentRel.lookup {mapping : LocationMap} {source residual : Dynamic.Environment}
    (related : EnvironmentRel mapping source residual) {id : Resolved.LocalId} {location : Dynamic.Location}
    (found : Dynamic.Environment.LooksUp source id location) :
    ∃ target, Dynamic.Environment.LooksUp residual id target ∧ Maps mapping location target := by
  induction related with
  | nil => cases found
  | cons mapped tail ih =>
      cases found with
      | head => exact ⟨_, .head, mapped⟩
      | tail different rest =>
          obtain ⟨target, read, locationEq⟩ := ih rest
          exact ⟨target, .tail different read, locationEq⟩

/-- An actual ordered suffix extension leaves every initial read byte-for-byte
unchanged; no heap cell is reconstructed from its type. -/
theorem initial_read {before after : Dynamic.Heap} {values : List Int}
    (cells : after.cells = before.cells ++ values.map integerCell)
    {location : Dynamic.Location} {cell : Dynamic.Cell} (read : Dynamic.Heap.Reads before location cell) :
    Dynamic.Heap.Reads after location cell := by
  cases read with
  | intro selected => exact .intro (cells ▸ selected.append_left)

end Solcore.SourceSemantics.CoreLowering.SourceStagingHeapRelation
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SourceStagedIntegerLetMeaning
/-! One accepted Integer let is erased from the resolved body while its source
execution allocates an ordinary Integer cell. Recursive body correctness is a
separate structural obligation. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.SourceStagedIntegerLetMeaning
open Frontend SourceInference SourceCoreElaboration
open SourceStagedClosedEvaluationMeaning SourceStagedIntegerStatementsMeaning
open SourceCoreElaboration.Internal

section Step
variable {program : Program} {context next : Context} {evidence : Dynamic.EvidenceEnvironment}
    {solved : List SolvedRequirement} {source : TypedSource} {scope : Resolved.Context}
    {actual : Staged.Environment} {environment : Dynamic.Environment} {before : Dynamic.Heap}
    {fuel : Nat} {expected : Core.Ty} {site : ErrorSite} {reason : ErrorReason}
    {statement : StatementId} {rest : List StatementId} {node : StatementNode}
    {binder : TypedBinder} {initializer : ExpressionId} {result : LoweredExpression}

/-- The actual compiler receipt and the independently typed source allocation
share the same initializer and full source heap. No tail execution law is used. -/
theorem let_source_step
    (receipt : Staged.IntegerLet.LetAccepted solved source scope actual fuel expected site reason
      statement rest node binder initializer result)
    (ledger : context.solvedRequirements = solved)
    (environments : EnvironmentRep actual environment before)
    (valid : UsedValid context solved result.consumedRequirements)
    (extension : BinderExtends source.owner context binder next) :
    ∃ initial body location after,
      Staged.integer solved source actual true fuel initializer = .ok initial ∧
      Staged.IntegerLet.lower solved source scope (Staged.Statements.bind binder initial.value :: actual)
        fuel expected site reason rest = .ok body ∧
      result.resolved = body.resolved ∧
      result.consumedRequirements = initial.consumedRequirements ++ body.consumedRequirements ∧
      Dynamic.ExpressionEvaluates program context evidence source environment before initializer (.integer initial.value) before ∧
      Dynamic.Heap.Allocates before .integer (some (.integer initial.value)) location after ∧
      Dynamic.StatementExecutes program context evidence source environment before statement next
        (.fallthrough ((binder.id, location) :: environment)) after ∧
      EnvironmentRep (Staged.Statements.bind binder initial.value :: actual)
        ((binder.id, location) :: environment) after ∧
      Extends before after [initial.value] := by
  cases receipt with
  | intro found form unit scopeFresh environmentFresh owned monomorphic binderType initialAccepted initialChecked bodyAccepted output =>
      rename_i initial body
      have used : UsedValid context solved initial.consumedRequirements := by
        apply valid.mono
        intro id member
        rw [output]
        exact List.mem_append_left _ member
      have evaluated := (checked_meaning (program := program) (evidence := evidence) ledger environments fuel).1 initialChecked used
      let location : Dynamic.Location := ⟨before.cells.length⟩
      let after : Dynamic.Heap := ⟨before.cells ++ [integerCell initial.value]⟩
      have allocated : Dynamic.Heap.Allocates before .integer (some (.integer initial.value)) location after := .append
      have bound : Dynamic.Binds environment before binder.id .integer (some (.integer initial.value))
          ((binder.id, location) :: environment) after := .intro allocated
      have represented := SourceStagedIntegerStatementsMeaning.EnvironmentRep.bind
        (Staged.Statements.bind binder initial.value) environments bound
      refine ⟨initial, body, location, after, initialAccepted, bodyAccepted,
        (by simpa using congrArg (fun r : LoweredExpression => r.resolved) output),
        (by simpa using congrArg (fun r : LoweredExpression => r.consumedRequirements) output),
        evaluated, allocated, ?_, represented, ?_⟩
      · exact .letInitialized (lookupStatement?_sound found) form evaluated monomorphic extension (binderType ▸ allocated)
      · simpa using (Extends.refl before).allocate allocated

/-- Acceptance supplies the initializer certificate; source typing supplies the
binder extension. These two facts are kept independent. -/
theorem let_of_accepted
    (accepted : Staged.IntegerLet.lower solved source scope actual (fuel + 1) expected site reason
      (statement :: rest) = .ok result)
    (found : source.lookupStatement? statement = some node)
    (form : node.form = .letDecl binder (some initializer))
    (binderType : binder.scheme.body = .integer)
    (ledger : context.solvedRequirements = solved)
    (environments : EnvironmentRep actual environment before)
    (valid : UsedValid context solved result.consumedRequirements)
    (extension : BinderExtends source.owner context binder next) :
    ∃ initial body location after,
      Staged.IntegerLet.LetAccepted solved source scope actual fuel expected site reason
        statement rest node binder initializer result ∧
      Staged.integer solved source actual true fuel initializer = .ok initial ∧
      Staged.IntegerLet.lower solved source scope (Staged.Statements.bind binder initial.value :: actual)
        fuel expected site reason rest = .ok body ∧
      result.resolved = body.resolved ∧
      result.consumedRequirements = initial.consumedRequirements ++ body.consumedRequirements ∧
      Dynamic.ExpressionEvaluates program context evidence source environment before initializer (.integer initial.value) before ∧
      Dynamic.Heap.Allocates before .integer (some (.integer initial.value)) location after ∧
      Dynamic.StatementExecutes program context evidence source environment before statement next
        (.fallthrough ((binder.id, location) :: environment)) after ∧
      EnvironmentRep (Staged.Statements.bind binder initial.value :: actual)
        ((binder.id, location) :: environment) after ∧ Extends before after [initial.value] := by
  have receipt := Staged.IntegerLet.let_of_accepted accepted found form binderType
  obtain ⟨initial, body, location, after, step⟩ := let_source_step (program := program) (evidence := evidence)
    receipt ledger environments valid extension
  exact ⟨initial, body, location, after, receipt, step⟩

/-- Actual source typing yields the exact extension used by the accepted head.
No source-context freshness follows merely from the compiler's duplicate check. -/
theorem typed_extension {control : ControlContext} {facts : StatementFacts}
    (unique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? statement = some node)
    (form : node.form = .letDecl binder (some initializer))
    (mono : binder.scheme.quantified = [])
    (typed : StatementHasType source control context statement next facts) :
    BinderExtends source.owner context binder next :=
  StaticViews.typed_let unique found form mono typed
end Step

/-- A public draft whose first source statement is an Integer let reaches the
same erased head. The returned draft keeps its complete unconsumed remainder. -/
theorem function_head_source_step
    {program : Program} {function : CheckedFunction} {draft : BodyDraft}
    {context next : Context} {evidence : Dynamic.EvidenceEnvironment}
    {environment : Dynamic.Environment} {before : Dynamic.Heap}
    {statement : StatementId} {rest : List StatementId} {node : StatementNode}
    {binder : TypedBinder} {initializer : ExpressionId}
    (accepted : lowerFunctionBody function = .ok draft)
    (roots : function.typedBody.roots = (statement :: rest).map NodeId.statement)
    (found : function.typedBody.lookupStatement? statement = some node)
    (form : node.form = .letDecl binder (some initializer))
    (binderType : binder.scheme.body = .integer)
    (ledger : context.solvedRequirements = function.solvedRequirements)
    (valid : UsedValid context function.solvedRequirements (function.solvedRequirements.map (·.id)))
    (extension : BinderExtends function.typedBody.owner context binder next) :
    Staged.IntegerLet.FunctionAccepted function draft ∧
    ∃ initial body location after,
      Staged.integer function.solvedRequirements function.typedBody [] true function.typedBody.nodes.length initializer = .ok initial ∧
      Staged.IntegerLet.lower function.solvedRequirements function.typedBody draft.inputs
        [Staged.Statements.bind binder initial.value] function.typedBody.nodes.length draft.returnType
        (match Staged.IntegerLet.lastStatement (statement :: rest) with
          | some last => .occurrence last.occurrence | none => .declaration function.declaration)
        .statementListFallthrough rest = .ok body ∧
      draft.resolved = body.resolved ∧
      reconcileConsumedRequirements function.declaration (function.solvedRequirements.map (·.id))
        (initial.consumedRequirements ++ body.consumedRequirements) = .ok draft.unconsumedRequirements ∧
      Dynamic.Heap.Allocates before .integer (some (.integer initial.value)) location after ∧
      Dynamic.StatementExecutes program context evidence function.typedBody environment before statement next
        (.fallthrough ((binder.id, location) :: environment)) after ∧
      EnvironmentRep [Staged.Statements.bind binder initial.value] ((binder.id, location) :: environment) after ∧
      Extends before after [initial.value] := by
  have receipt := Staged.IntegerLet.function_of_accepted accepted
  refine ⟨receipt, ?_⟩
  cases receipt with
  | intro owned rootsAccepted rootsSame nonempty inputsAccepted expectedAccepted bodyAccepted reconciled declaration inputEq resolved returnType rootOccurrence =>
      rename_i statements head tail inputs expected lowered
      rw [nonempty] at rootsSame bodyAccepted
      have same : head :: tail = statement :: rest :=
        (List.map_inj_right (fun a b h => NodeId.statement.inj h)).mp (rootsSame.trans roots)
      obtain ⟨rfl, rfl⟩ := List.cons.inj same
      have used : UsedValid context function.solvedRequirements lowered.consumedRequirements := by
        intro row proof member consumed implementation
        exact valid row proof member (List.mem_map.mpr ⟨row, member, rfl⟩) implementation
      have letReceipt := Staged.IntegerLet.let_of_accepted bodyAccepted found form binderType
      obtain ⟨initial, body, location, after, initialEq, bodyEq, resultEq, consumedEq, evaluated,
        allocated, executed, represented, cells⟩ := let_source_step (program := program) (evidence := evidence)
          letReceipt ledger (EnvironmentRep.empty environment before) used extension
      refine ⟨initial, body, location, after, initialEq, ?_, resolved.trans resultEq, ?_, allocated, executed, represented, cells⟩
      · cases lastEq : Staged.IntegerLet.lastStatement (head :: tail) <;>
          simpa only [inputEq, returnType, lastEq] using bodyEq
      · exact consumedEq ▸ reconciled


/-- The actual accepted let authorizes exactly this source-only Integer cell.
The residual heap and every retained cell/capture remain related by the fixed
structural relation. The ordinary closed source step needs no mapping premise. -/
theorem let_erased_step
    {program : Program} {context next : Context} {evidence : Dynamic.EvidenceEnvironment}
    {solved : List SolvedRequirement} {source : TypedSource} {scope : Resolved.Context}
    {actual : Staged.Environment} {environment : Dynamic.Environment} {before residual : Dynamic.Heap}
    {mapping : SourceStagingHeapRelation.LocationMap}
    {fuel : Nat} {expected : Core.Ty} {site : ErrorSite} {reason : ErrorReason}
    {statement : StatementId} {rest : List StatementId} {node : StatementNode}
    {binder : TypedBinder} {initializer : ExpressionId} {result : LoweredExpression}
    (receipt : Staged.IntegerLet.LetAccepted solved source scope actual fuel expected site reason
      statement rest node binder initializer result)
    (ledger : context.solvedRequirements = solved)
    (environments : EnvironmentRep actual environment before)
    (valid : UsedValid context solved result.consumedRequirements)
    (extension : BinderExtends source.owner context binder next)
    (related : SourceStagingHeapRelation.HeapRel mapping before residual) :
    ∃ initial body location after,
      Staged.integer solved source actual true fuel initializer = .ok initial ∧
      Staged.IntegerLet.lower solved source scope (Staged.Statements.bind binder initial.value :: actual)
        fuel expected site reason rest = .ok body ∧
      result.resolved = body.resolved ∧
      result.consumedRequirements = initial.consumedRequirements ++ body.consumedRequirements ∧
      Dynamic.ExpressionEvaluates program context evidence source environment before initializer (.integer initial.value) before ∧
      Dynamic.Heap.Allocates before .integer (some (.integer initial.value)) location after ∧
      Dynamic.StatementExecutes program context evidence source environment before statement next
        (.fallthrough ((binder.id, location) :: environment)) after ∧
      EnvironmentRep (Staged.Statements.bind binder initial.value :: actual)
        ((binder.id, location) :: environment) after ∧
      Extends before after [initial.value] ∧
      SourceStagingHeapRelation.HeapRel (mapping ++ [none]) after residual := by
  obtain ⟨initial, body, location, after, initialEq, bodyEq, output, consumed, evaluated,
    allocated, executed, represented, cells⟩ := let_source_step (program := program) (evidence := evidence)
      receipt ledger environments valid extension
  exact ⟨initial, body, location, after, initialEq, bodyEq, output, consumed, evaluated,
    allocated, executed, represented, cells, related.erase_allocated allocated⟩

end Solcore.SourceSemantics.CoreLowering.SourceStagedIntegerLetMeaning
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SourceStagedIntegerResidualMeaning
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.SourceStagedIntegerResidualMeaning
open Frontend SourceInference Solcore.SourceSemantics.Dynamic

/-- Parameter allocation retains all reads, including unused original cells. -/
theorem preserves_read {initial final : Dynamic.Environment} {before after : Heap}
    {inputs : List TypedBinder} {values : List Dynamic.Value}
    (allocated : BindersAllocate initial before inputs values final after)
    {location : Location} {cell : Cell} (read : Heap.Reads before location cell) :
    Heap.Reads after location cell := by
  induction allocated with
  | nil => exact read
  | cons allocation _ ih => exact ih (allocation.preserves_read read)

theorem allocation_length {initial final : Dynamic.Environment} {before after : Heap}
    {inputs : List TypedBinder} {values : List Dynamic.Value}
    (allocated : BindersAllocate initial before inputs values final after) :
    inputs.length = values.length := by
  induction allocated with
  | nil => rfl
  | cons _ _ ih => exact congrArg Nat.succ ih

/-- A fresh parameter sequence preserves the original first-match lookup. -/
theorem preserves_lookup {initial final : Dynamic.Environment} {before after : Heap}
    {inputs : List TypedBinder} {values : List Dynamic.Value}
    (allocated : BindersAllocate initial before inputs values final after)
    {id : Resolved.LocalId} {location : Location}
    (fresh : ∀ input, input ∈ inputs → input.id ≠ id)
    (found : Dynamic.Environment.LooksUp initial id location) :
    Dynamic.Environment.LooksUp final id location := by
  induction allocated with
  | nil => exact found
  | cons allocation tail ih =>
      exact ih (fun input member => fresh input (by simp [member]))
        (.tail (fresh _ (by simp)) found)

/-- Forward input order selects the actual source address, even though the
completed lexical environment lists the last allocated parameter first. -/
theorem allocated_lookup {initial final : Dynamic.Environment} {before after : Heap}
    {inputs : List TypedBinder} {values : List Dynamic.Value}
    (allocated : BindersAllocate initial before inputs values final after)
    (unique : (inputs.map (·.id)).Nodup)
    {index : Nat} {input : TypedBinder} {value : Dynamic.Value}
    (inputAt : inputs[index]? = some input) (valueAt : values[index]? = some value) :
    ∃ location : Location, location.index = before.cells.length + index ∧
      Dynamic.Environment.LooksUp final input.id location ∧
      Heap.Reads after location { type := input.scheme.body, value := some value } := by
  induction allocated generalizing index input value with
  | nil => simp at inputAt
  | @cons initial final before middle after head rest headValue tailValues location allocation tail ih =>
      simp only [List.map_cons, List.nodup_cons] at unique
      cases index with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at inputAt valueAt
          subst input
          subst value
          refine ⟨location, by simpa using allocation.location_fresh, ?_, ?_⟩
          · apply preserves_lookup tail ?_ Dynamic.Environment.LooksUp.head
            intro candidate member same
            exact unique.1 (List.mem_map.mpr ⟨candidate, member, same⟩)
          · exact preserves_read tail allocation.reads_new
      | succ index =>
          obtain ⟨actual, address, found, read⟩ := ih unique.2 inputAt valueAt
          refine ⟨actual, ?_, found, read⟩
          rw [allocation.length_eq_succ] at address
          omega

/-- Scalar input values are represented directly by the pure Core ABI.
This relation supplies no Core store allocation or callable authority. -/
inductive ScalarRep : Dynamic.Value → Core.Value → Prop where
  | word (value : Core.Word) : ScalarRep (.word value) (.word value)
  | bool (value : Bool) : ScalarRep (.bool value) (.bool value)

inductive ScalarValuesRep : List Dynamic.Value → List Core.Value → Prop where
  | nil : ScalarValuesRep [] []
  | cons {value : Dynamic.Value} {native : Core.Value}
      {values : List Dynamic.Value} {natives : List Core.Value}
      (head : ScalarRep value native) (tail : ScalarValuesRep values natives) :
      ScalarValuesRep (value :: values) (native :: natives)

theorem ScalarValuesRep.length_eq {values : List Dynamic.Value} {native : List Core.Value}
    (represented : ScalarValuesRep values native) : values.length = native.length := by
  induction represented with
  | nil => rfl
  | cons _ _ ih => exact congrArg Nat.succ ih

theorem scalar_at {values : List Dynamic.Value} {native : List Core.Value}
    (represented : ScalarValuesRep values native)
    {index : Nat} {result : Core.Value} (atNative : native[index]? = some result) :
    ∃ value, values[index]? = some value ∧ ScalarRep value result := by
  induction represented generalizing index with
  | nil => simp at atNative
  | cons head tail ih =>
      cases index with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at atNative
          subst result
          exact ⟨_, rfl, head⟩
      | succ index => exact ih atNative

/-- The pure positional ABI keeps the original forward parameter order. -/
def inputEnvironment (inputs : List TypedBinder) (native : List Core.Value) :
    Resolved.LocalScope Core.Value := (inputs.map (·.id)).zip native

/-- An actual scalar ABI lookup is authenticated by the actual source
parameter allocator. Neither the initial environment nor unused cells are
filtered; this theorem does not allocate any Core store cells. -/
theorem allocated_native_lookup {initial final : Dynamic.Environment} {before after : Heap}
    {inputs : List TypedBinder} {values : List Dynamic.Value} {native : List Core.Value}
    (allocated : BindersAllocate initial before inputs values final after)
    (unique : (inputs.map (·.id)).Nodup)
    (represented : ScalarValuesRep values native)
    {id : Resolved.LocalId} {result : Core.Value}
    (found : Resolved.LocalScope.Lookup (inputEnvironment inputs native) id result) :
    ∃ location cell value,
      Dynamic.Environment.LooksUp final id location ∧ Heap.Reads after location cell ∧
      cell.generalized = none ∧ cell.value = some value ∧ ScalarRep value result := by
  have arity : (inputs.map (·.id)).length = native.length := by
    rw [List.length_map]
    exact (allocation_length allocated).trans represented.length_eq
  have idsEq : Resolved.LocalScope.ids (inputEnvironment inputs native) = inputs.map (·.id) :=
    List.map_fst_zip (Nat.le_of_eq arity)
  have valuesEq : Resolved.LocalScope.values (inputEnvironment inputs native) = native :=
    List.map_snd_zip (Nat.le_of_eq arity.symm)
  obtain ⟨index, indexed, nativeAt⟩ := found.indexed
  rw [idsEq] at indexed
  rw [valuesEq] at nativeAt
  have inputIdAt := indexed.getElem?
  rw [List.getElem?_map] at inputIdAt
  obtain ⟨input, inputAt, sameId⟩ := Option.map_eq_some_iff.mp inputIdAt
  obtain ⟨value, valueAt, scalar⟩ := scalar_at represented nativeAt
  obtain ⟨location, _, lookup, read⟩ := allocated_lookup allocated unique inputAt valueAt
  exact ⟨location, _, value, sameId ▸ lookup, read, rfl, rfl, scalar⟩

end Solcore.SourceSemantics.CoreLowering.SourceStagedIntegerResidualMeaning

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.SourceStagedIntegerResidualMeaning
open Frontend SourceInference SourceCoreElaboration.Internal.Staged

/-- Only the two scalar carriers used by this pure residual fragment. -/
inductive ScalarTyped : Core.Value → Core.Ty → Prop where
  | word (value : Core.Word) : ScalarTyped (.word value) .word
  | bool (value : Bool) : ScalarTyped (.bool value) .bool

/-- Every actual native first-match lookup observes the same ordinary Source cell. -/
def RuntimeEnvironmentRep (native : Resolved.Environment) (source : Dynamic.Environment)
    (heap : Dynamic.Heap) : Prop :=
  ∀ id value, Resolved.LocalScope.Lookup native id value → ∃ location cell sourceValue,
    Dynamic.Environment.LooksUp source id location ∧ Dynamic.Heap.Reads heap location cell ∧
    cell.generalized = none ∧ cell.value = some sourceValue ∧ ScalarRep sourceValue value

/-- Context entries have actual native scalar values of their assigned types. -/
def RuntimeEnvironmentTyped (scope : Resolved.Context) (native : Resolved.Environment) : Prop :=
  ∀ id type, Resolved.LocalScope.Lookup scope id type → ∃ value,
    Resolved.LocalScope.Lookup native id value ∧ ScalarTyped value type

private theorem scalar_of_raw {program : Program} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
    {environment : Dynamic.Environment} {heap : Dynamic.Heap} {id : ExpressionId}
    {node : ExpressionNode} {value : Dynamic.Value}
    (found : source.lookupExpression? id = some node) (empty : node.coercions = [])
    (raw : Dynamic.ExpressionFormEvaluates program context evidence source environment heap
      node.form node.requirements node.coercions value heap) :
    Dynamic.ExpressionEvaluates program context evidence source environment heap id value heap := by
  apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound found) raw
  rw [empty]
  exact .nil

/-- One induction on the static receipt constructs independent Source and
Resolved evaluations. Both keep their full initial states. A native store is
independent of the Source heap and no Core allocation is inferred here. -/
theorem expression_meaning {program : Program} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {solved : List SolvedRequirement} {source : TypedSource}
    {scope : Resolved.Context} {staged : SourceCoreElaboration.Internal.Staged.Environment}
    {fuel : Nat} {id : ExpressionId} {result : SourceCoreElaboration.LoweredExpression}
    {expected : Core.Ty} {sourceEnv : Dynamic.Environment} {sourceHeap : Dynamic.Heap}
    {nativeEnv : Resolved.Environment} {coreStore : Core.Store}
    (checked : Residual.ExpressionChecked solved source scope staged fuel id result)
    (typed : Resolved.HasType scope result.resolved expected)
    (ledger : context.solvedRequirements = solved)
    (valid : SourceStagedClosedEvaluationMeaning.UsedValid context solved result.consumedRequirements)
    (stagedRep : SourceStagedClosedEvaluationMeaning.EnvironmentRep staged sourceEnv sourceHeap)
    (runtimeRep : RuntimeEnvironmentRep nativeEnv sourceEnv sourceHeap)
    (typedEnv : RuntimeEnvironmentTyped scope nativeEnv) :
    ∃ sourceValue nativeValue,
      Dynamic.ExpressionEvaluates program context evidence source sourceEnv sourceHeap id sourceValue sourceHeap ∧
      Resolved.Evaluates nativeEnv coreStore result.resolved nativeValue coreStore ∧
      ScalarRep sourceValue nativeValue ∧ ScalarTyped nativeValue expected := by
  induction checked generalizing expected with
  | @literal fuel id node literal value found form requirements coercions interpreted =>
    cases typed
    have modulo : Core.Word.ofNatModulo value.val = value := by
      apply Fin.ext
      exact Nat.mod_eq_of_lt value.isLt
    have constructs : Dynamic.LiteralConstructs literal (.word value) := by
      rw [← modulo]
      exact .word (interpretWordLiteral?_sound interpreted)
    refine ⟨.word value, .word value, ?_, .word, .word value, .word value⟩
    apply scalar_of_raw found coercions
    rw [form, requirements, coercions]
    exact .literal rfl constructs
  | @stagedWord fuel id result checked =>
    cases typed
    exact ⟨.word result.value, .word result.value,
      (SourceStagedClosedEvaluationMeaning.checked_meaning ledger stagedRep fuel).2.1 checked valid,
      .word, .word result.value, .word result.value⟩
  | @stagedBool fuel id result checked =>
    cases typed
    exact ⟨.bool result.value, .bool result.value,
      (SourceStagedClosedEvaluationMeaning.checked_meaning ledger stagedRep fuel).2.2 checked valid,
      .bool, .bool result.value, .bool result.value⟩
  | @«local» fuel id node name binder found form requirements coercions _ =>
    cases typed with
    | var atType =>
      obtain ⟨nativeValue, atValue, valueTyped⟩ := typedEnv _ _ atType
      obtain ⟨location, cell, sourceValue, lookup, read, ordinary, initialized, scalar⟩ := runtimeRep _ _ atValue
      refine ⟨sourceValue, nativeValue, ?_, .var atValue, scalar, valueTyped⟩
      apply scalar_of_raw found coercions
      rw [form, requirements, coercions]
      exact .local rfl lookup read ordinary initialized
  | @boolean fuel id node name value found form requirements coercions =>
    cases typed
    refine ⟨.bool value, .bool value, ?_, .bool, .bool value, .bool value⟩
    apply scalar_of_raw found coercions
    rw [form, requirements, coercions]
    exact .builtinBoolean rfl
  | @group fuel id node inner result found form requirements coercions child ih =>
    obtain ⟨sourceValue, nativeValue, evaluated, native, scalar, valueTyped⟩ := ih typed valid
    refine ⟨sourceValue, nativeValue, ?_, native, scalar, valueTyped⟩
    apply scalar_of_raw found coercions
    rw [form, requirements, coercions]
    exact .group rfl evaluated
  | @conditional fuel id node condition yes no guard left right found form requirements coercions _ _ _ guardIH yesIH noIH =>
    cases typed with
    | ifE guardTyped yesTyped noTyped =>
      have guardValid := valid.mono (by intro child member; exact List.mem_append_left _ (List.mem_append_left _ member))
      have yesValid := valid.mono (by intro child member; exact List.mem_append_left _ (List.mem_append_right _ member))
      have noValid := valid.mono (by intro child member; exact List.mem_append_right _ member)
      obtain ⟨guardSource, guardNative, guardSourceEval, guardNativeEval, guardScalar, guardType⟩ := guardIH guardTyped guardValid
      cases guardType with
      | bool truth =>
        cases guardScalar
        cases truth with
        | false =>
          obtain ⟨sourceValue, nativeValue, evaluated, native, scalar, valueTyped⟩ := noIH noTyped noValid
          refine ⟨sourceValue, nativeValue, ?_, .ifFalse guardNativeEval native, scalar, valueTyped⟩
          apply scalar_of_raw found coercions
          rw [form, requirements, coercions]
          exact .conditionalFalse rfl guardSourceEval evaluated
        | true =>
          obtain ⟨sourceValue, nativeValue, evaluated, native, scalar, valueTyped⟩ := yesIH yesTyped yesValid
          refine ⟨sourceValue, nativeValue, ?_, .ifTrue guardNativeEval native, scalar, valueTyped⟩
          apply scalar_of_raw found coercions
          rw [form, requirements, coercions]
          exact .conditionalTrue rfl guardSourceEval evaluated

end Solcore.SourceSemantics.CoreLowering.SourceStagedIntegerResidualMeaning

set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.SourceStagedIntegerResidualMeaning
open Solcore Frontend SourceInference SourceSemantics
open SourceCoreElaboration SourceCoreElaboration.Internal
open SourceStagingHeapRelation
local notation "Closed" => SourceStagedClosedEvaluationMeaning.EnvironmentRep

/-- Root lexical rows may omit only an actual staged Integer binding. Captured
closure environments continue to use the unchanged full EnvironmentRel. -/
inductive MixedEnvironment (mapping : LocationMap) (heap : Dynamic.Heap) :
    Dynamic.Environment → Dynamic.Environment → Staged.Environment → Prop where
  | nil : MixedEnvironment mapping heap [] [] []
  | keep {id source target left right staged}
      (mapped : Maps mapping source target)
      (tail : MixedEnvironment mapping heap left right staged) :
      MixedEnvironment mapping heap ((id, source) :: left) ((id, target) :: right) staged
  | erase {binding location left right staged}
      (dropped : mapping[location.index]? = some none)
      (read : Dynamic.Heap.Reads heap location
        { type := .integer, value := some (.integer (SourceStagedClosedEvaluationMeaning.bindingValue binding)) })
      (tail : MixedEnvironment mapping heap left right staged) :
      MixedEnvironment mapping heap
        ((SourceStagedIntegerStatementsMeaning.bindingId binding, location) :: left)
        right (binding :: staged)

namespace MixedEnvironment

theorem of_retained {mapping : LocationMap} {heap : Dynamic.Heap}
    {left right : Dynamic.Environment} (related : EnvironmentRel mapping left right) :
    MixedEnvironment mapping heap left right [] := by
  induction related with
  | nil => exact .nil
  | cons mapped tail ih => exact .keep mapped ih

/-- All old rows survive the original source allocation, including shadowed
and unused entries. The new mapping position is accounted for separately. -/
theorem allocated {mapping : LocationMap} {before after : Dynamic.Heap}
    {left right : Dynamic.Environment} {staged : Staged.Environment}
    (related : MixedEnvironment mapping before left right staged)
    {type : TypeSystem.Ty} {value : Option Dynamic.Value} {location : Dynamic.Location}
    (allocation : Dynamic.Heap.Allocates before type value location after)
    (suffix : LocationMap) : MixedEnvironment (mapping ++ suffix) after left right staged := by
  induction related with
  | nil => exact .nil
  | keep mapped tail ih => exact .keep (extends_append _ _ _ _ mapped) ih
  | erase dropped read tail ih =>
      apply MixedEnvironment.erase ?_ (allocation.preserves_read read) ih
      simpa only [List.getElem?_append_left (List.getElem?_eq_some_iff.mp dropped).1] using dropped

theorem erase_allocated {mapping : LocationMap} {before residual after : Dynamic.Heap}
    {left right : Dynamic.Environment} {staged : Staged.Environment}
    (related : MixedEnvironment mapping before left right staged)
    (heaps : HeapRel mapping before residual) (binding : Staged.Binding)
    {location : Dynamic.Location}
    (allocation : Dynamic.Heap.Allocates before .integer
      (some (.integer (SourceStagedClosedEvaluationMeaning.bindingValue binding))) location after) :
    MixedEnvironment (mapping ++ [none]) after
      ((SourceStagedIntegerStatementsMeaning.bindingId binding, location) :: left)
      right (binding :: staged) := by
  apply MixedEnvironment.erase ?_ allocation.reads_new (related.allocated allocation [none])
  rw [allocation.location_fresh, ← heaps.length]
  exact List.getElem?_concat_length

end MixedEnvironment

/-- Independent typing of the actual final artifact follows from its own
positional lowering receipt and Core type reconstruction. -/
theorem artifact_typed (artifact : ElaboratedFunction) :
    Resolved.HasType artifact.inputs artifact.resolved artifact.returnType :=
  (Resolved.Expr.lower?_sound artifact.resolvedLowered).reflects_type
    (Core.infer_sound artifact.coreTypeChecked)

end Solcore.SourceSemantics.CoreLowering.SourceStagedIntegerResidualMeaning

namespace Solcore.SourceSemantics.CoreLowering.SourceStagedIntegerResidualMeaning
open Solcore Frontend SourceInference SourceSemantics SourceCoreElaboration
open SourceCoreElaboration.Internal

/-- Source typing is an independent premise; actual projection only selects
the matching scalar carrier for the pure ABI. -/
theorem scalar_typed_of_source {context : SourceSemantics.Context} {heap : Dynamic.Heap}
    {value : Dynamic.Value} {native : Core.Value} {sourceType : TypeSystem.Ty}
    {type : Core.Ty} {site : ErrorSite}
    (represented : ScalarRep value native) (typed : Dynamic.ValueHasType context heap value sourceType)
    (projected : lowerType site sourceType = .ok type) : ScalarTyped native type := by
  cases represented <;> cases typed <;> cases projected <;> constructor

/-- The source Integer allocation preserves every runtime-variable observation;
its new identity is absent from the actual native input scope. -/
theorem RuntimeEnvironmentRep.bind {native : Resolved.Environment} {scope : Resolved.Context}
    {source : Dynamic.Environment} {before after : Dynamic.Heap}
    (related : RuntimeEnvironmentRep native source before)
    (sameIds : native.ids = scope.ids) (binder : TypedBinder)
    (fresh : scope.ids.contains binder.id = false)
    {value : Int} {location : Dynamic.Location}
    (allocated : Dynamic.Heap.Allocates before .integer (some (.integer value)) location after) :
    RuntimeEnvironmentRep native ((binder.id, location) :: source) after := by
  intro id value found
  obtain ⟨index, indexed, _⟩ := found.indexed
  have member : id ∈ scope.ids := by
    rw [← sameIds]
    exact List.mem_of_getElem? indexed.getElem?
  have different : binder.id ≠ id := by
    intro same
    subst id
    have absent : binder.id ∉ scope.ids := by simpa using fresh
    exact absent member
  obtain ⟨oldLocation, cell, sourceValue, lookup, read, ordinary, initialized, scalar⟩ := related _ _ found
  exact ⟨oldLocation, cell, sourceValue, .tail different lookup, allocated.preserves_read read,
    ordinary, initialized, scalar⟩

theorem inputs_ids {seen : List Resolved.LocalId} {inputs : List TypedBinder} {scope : Resolved.Context}
    (checked : Staged.Residual.InputsChecked seen inputs scope) : scope.ids = inputs.map (·.id) := by
  induction checked with
  | nil => rfl
  | cons fresh mono projected tail ih => simpa only [Resolved.LocalScope.ids, List.map_cons] using congrArg (List.cons _) ih

theorem inputs_unique_aux {seen : List Resolved.LocalId} {inputs : List TypedBinder} {scope : Resolved.Context}
    (checked : Staged.Residual.InputsChecked seen inputs scope) :
    (inputs.map (·.id)).Nodup ∧ ∀ id, id ∈ inputs.map (·.id) → id ∉ seen := by
  induction checked with
  | nil => exact ⟨by simp, by simp⟩
  | @cons seen binder rest type scope fresh mono projected tail ih =>
    have absent : binder.id ∉ seen := by simpa using fresh
    refine ⟨?_, ?_⟩
    · simp only [List.map_cons, List.nodup_cons]
      exact ⟨fun member => (ih.2 _ member) (by simp), ih.1⟩
    · intro id member
      rcases List.mem_cons.mp member with same | member
      · simpa only [same] using absent
      · exact fun inSeen => (ih.2 _ member) (List.mem_cons_of_mem _ inSeen)

/-- Scalar values are typed using the original source parameter types and the
actual ordered lowerInputs receipt, not from native payloads alone. -/
theorem inputs_typed {seen : List Resolved.LocalId} {inputs : List TypedBinder} {scope : Resolved.Context}
    (checked : Staged.Residual.InputsChecked seen inputs scope)
    {context : SourceSemantics.Context} {heap : Dynamic.Heap}
    {values : List Dynamic.Value} {native : List Core.Value}
    (typed : Dynamic.ValuesHaveTypes context heap values (inputs.map (fun binder => binder.scheme.body)))
    (represented : ScalarValuesRep values native) :
    RuntimeEnvironmentTyped scope (inputEnvironment inputs native) := by
  induction checked generalizing values native with
  | nil =>
    cases typed
    cases represented
    intro id type found
    cases found
  | cons fresh mono projected tail ih =>
    cases typed with
    | cons headTyped tailTyped =>
      cases represented with
      | cons headRep tailRep =>
        have tailEnv := ih tailTyped tailRep
        intro id type found
        cases found with
        | head => exact ⟨_, .head, scalar_typed_of_source headRep headTyped projected⟩
        | tail different found =>
          obtain ⟨value, foundValue, valueTyped⟩ := tailEnv _ _ found
          exact ⟨value, .tail different foundValue, valueTyped⟩

end Solcore.SourceSemantics.CoreLowering.SourceStagedIntegerResidualMeaning

namespace Solcore.SourceSemantics.CoreLowering.SourceStagedIntegerResidualMeaning
open Solcore Frontend SourceInference SourceSemantics SourceCoreElaboration
open SourceCoreElaboration.Internal SourceStagingHeapRelation

theorem scalar_identity {mapping : LocationMap} {value : Dynamic.Value} {native : Core.Value}
    (represented : ScalarRep value native) : ValueRel mapping value value := by
  cases represented with
  | word value => exact .word value
  | bool value => exact .bool value

/-- Runtime input cells are kept by the two actual Source allocators. This
statement supplies no Core store allocation. -/
theorem inputs_heaps {mapping : LocationMap}
    {before residual after afterResidual : Dynamic.Heap}
    {initial initialResidual final finalResidual : Dynamic.Environment}
    {inputs : List TypedBinder} {values : List Dynamic.Value} {native : List Core.Value}
    (heaps : HeapRel mapping before residual)
    (environments : MixedEnvironment mapping before initial initialResidual [])
    (allocated : Dynamic.BindersAllocate initial before inputs values final after)
    (residualAllocated : Dynamic.BindersAllocate initialResidual residual inputs values finalResidual afterResidual)
    (represented : ScalarValuesRep values native) :
    ∃ finalMap, HeapRel finalMap after afterResidual ∧
      MixedEnvironment finalMap after final finalResidual [] := by
  induction allocated generalizing mapping residual initialResidual finalResidual afterResidual native with
  | nil =>
    cases residualAllocated
    exact ⟨mapping, heaps, environments⟩
  | @cons initial final before middle after binder rest value values location allocation tail ih =>
    cases residualAllocated with
    | @cons _ _ _ residualMiddle _ _ _ _ _ residualLocation residualAllocation residualTail =>
      cases represented with
      | cons headRep tailRep =>
        have nextHeaps := heaps.keep_allocated (scalar_identity headRep) allocation residualAllocation
        have oldEnvironments := environments.allocated allocation [some residualLocation]
        have mapped : Maps (mapping ++ [some residualLocation]) location residualLocation := by
          unfold Maps
          rw [allocation.location_fresh, ← heaps.length]
          exact List.getElem?_concat_length
        exact ih nextHeaps (.keep mapped oldEnvironments) residualTail tailRep

theorem input_environment_ids {initial final : Dynamic.Environment} {before after : Dynamic.Heap}
    {inputs : List TypedBinder} {values : List Dynamic.Value} {native : List Core.Value}
    {scope : Resolved.Context}
    (allocated : Dynamic.BindersAllocate initial before inputs values final after)
    (represented : ScalarValuesRep values native)
    (checked : Staged.Residual.InputsChecked [] inputs scope) :
    (inputEnvironment inputs native).ids = scope.ids := by
  rw [inputs_ids checked]
  apply List.map_fst_zip
  simpa only [List.length_map] using Nat.le_of_eq ((allocation_length allocated).trans represented.length_eq)

end Solcore.SourceSemantics.CoreLowering.SourceStagedIntegerResidualMeaning

/-! Independent source typing supplies lexical extensions on the actual
residual statement receipt, including both conditional branches. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.SourceStagedIntegerResidualMeaning
open Core Frontend SourceInference
open SourceCoreElaboration SourceCoreElaboration.Internal

inductive BindingsFormed (solved : List SolvedRequirement) (source : TypedSource)
    (scope : Resolved.Context) : SourceSemantics.Context →
    {actual : Staged.Environment} → {fuel : Nat} → {roots : List StatementId} →
    {result : LoweredExpression} →
    Staged.Residual.StatementsChecked solved source scope actual fuel roots result → Prop where
  | letValue {actual : Staged.Environment} {fuel : Nat}
      {statement : StatementId} {rest : List StatementId} {node : StatementNode}
      {binder : TypedBinder} {initializer : ExpressionId}
      {initial : StagedIntegerEvaluation} {result : LoweredExpression}
      {context next : SourceSemantics.Context}
      (found : source.lookupStatement? statement = some node)
      (form : node.form = .letDecl binder (some initializer)) (unit : node.type = .unit)
      (scopeFresh : scope.ids.contains binder.id = false)
      (environmentFresh : Staged.IntegerLet.contains actual binder.id = false)
      (owned : binder.id.owner = source.owner) (monomorphic : binder.scheme.quantified = [])
      (binderType : binder.scheme.body = .integer)
      (initialChecked : Staged.IntegerChecked solved source actual true fuel initializer initial)
      (bodyChecked : Staged.Residual.StatementsChecked solved source scope
        (Staged.Statements.bind binder initial.value :: actual) fuel rest result)
      (extension : BinderExtends source.owner context binder next)
      (bodyFormed : BindingsFormed solved source scope next bodyChecked) :
      BindingsFormed solved source scope context
        (.letValue found form unit scopeFresh environmentFresh owned monomorphic binderType initialChecked bodyChecked)
  | returnValue {actual : Staged.Environment} {fuel : Nat}
      {statement : StatementId} {node : StatementNode} {value : ExpressionId}
      {result : LoweredExpression} {context : SourceSemantics.Context}
      (found : source.lookupStatement? statement = some node)
      (form : node.form = .returnStmt (some value))
      (valueChecked : Staged.Residual.ExpressionChecked solved source scope actual fuel value result) :
      BindingsFormed solved source scope context (.returnValue found form valueChecked)
  | conditional {actual : Staged.Environment} {fuel : Nat}
      {statement : StatementId} {node : StatementNode} {condition : ExpressionId}
      {yes no : List StatementId} {guard left right : LoweredExpression}
      {context : SourceSemantics.Context}
      (found : source.lookupStatement? statement = some node)
      (form : node.form = .ifThen condition yes (some no))
      (conditionChecked : Staged.Residual.ExpressionChecked solved source scope actual fuel condition guard)
      (thenChecked : Staged.Residual.StatementsChecked solved source scope actual fuel yes left)
      (elseChecked : Staged.Residual.StatementsChecked solved source scope actual fuel no right)
      (thenFormed : BindingsFormed solved source scope context thenChecked)
      (elseFormed : BindingsFormed solved source scope context elseChecked) :
      BindingsFormed solved source scope context (.conditional found form conditionChecked thenChecked elseChecked)
  | block {actual : Staged.Environment} {fuel : Nat}
      {statement : StatementId} {node : StatementNode} {body : List StatementId}
      {result : LoweredExpression} {context : SourceSemantics.Context}
      (found : source.lookupStatement? statement = some node) (form : node.form = .block body)
      (bodyChecked : Staged.Residual.StatementsChecked solved source scope actual fuel body result)
      (bodyFormed : BindingsFormed solved source scope context bodyChecked) :
      BindingsFormed solved source scope context (.block found form bodyChecked)

theorem checked_nonempty {solved source scope actual fuel roots result}
    (checked : Staged.Residual.StatementsChecked solved source scope actual fuel roots result) :
    roots ≠ [] := by
  cases checked <;> simp

/-- Source typing and the original unique node lookup identify the same binders
in the accepted tree. The residual scope and staged environment remain fixed. -/
theorem bindingsFormed_of_typing {solved : List SolvedRequirement} {source : TypedSource}
    {scope : Resolved.Context} {actual : Staged.Environment} {fuel : Nat}
    {roots : List StatementId} {result : LoweredExpression}
    (checked : Staged.Residual.StatementsChecked solved source scope actual fuel roots result)
    (unique : NodeOccurrencesUnique source) {control : ControlContext}
    {context final : SourceSemantics.Context} {facts : BodyFacts}
    (typed : StatementsHaveType source control context roots final facts) :
    BindingsFormed solved source scope context checked := by
  induction checked generalizing context final facts with
  | letValue found form unit scopeFresh environmentFresh owned mono binderType initial body ih =>
      obtain ⟨next, headFacts, tailFacts, head, tail⟩ :=
        SourceStagedIntegerStatementsMeaning.StaticViews.typed_cons typed (checked_nonempty body)
      exact .letValue found form unit scopeFresh environmentFresh owned mono binderType initial body
        (SourceStagedIntegerStatementsMeaning.StaticViews.typed_let unique found form mono head) (ih tail)
  | returnValue found form value => exact .returnValue found form value
  | conditional found form condition yes no ihYes ihNo =>
      obtain ⟨headFacts, head⟩ := SourceStagedIntegerStatementsMeaning.StaticViews.typed_singleton typed
      obtain ⟨yesFinal, noFinal, yesFacts, noFacts, yesTyped, noTyped⟩ :=
        SourceStagedIntegerStatementsMeaning.StaticViews.typed_if unique found form head
      exact .conditional found form condition yes no (ihYes yesTyped) (ihNo noTyped)
  | block found form body ih =>
      obtain ⟨headFacts, head⟩ := SourceStagedIntegerStatementsMeaning.StaticViews.typed_singleton typed
      obtain ⟨inner, innerFacts, bodyTyped⟩ :=
        SourceStagedIntegerStatementsMeaning.StaticViews.typed_block unique found form head
      exact .block found form body (ih bodyTyped)

end Solcore.SourceSemantics.CoreLowering.SourceStagedIntegerResidualMeaning

namespace Solcore.SourceSemantics.CoreLowering.SourceStagedIntegerResidualMeaning
open Solcore Frontend SourceInference SourceSemantics SourceCoreElaboration
open SourceCoreElaboration.Internal
open SourceStagedClosedEvaluationMeaning SourceStagedIntegerStatementsMeaning
open SourceStagingHeapRelation

/-- The sole structural statement proof executes only the selected Source
branch, records every Integer cell in order, and evaluates the actual residual
expression in an independent unchanged Core store. Expression meaning is
closed by expression_meaning; there is no caller or body execution premise. -/
theorem formed_meaning {solved : List SolvedRequirement} {source : TypedSource}
    {scope : Resolved.Context} {staged : Staged.Environment} {fuel : Nat}
    {roots : List StatementId} {result : LoweredExpression}
    {checked : Staged.Residual.StatementsChecked solved source scope staged fuel roots result}
    {context : SourceSemantics.Context} (formed : BindingsFormed solved source scope context checked)
    {program : Program} {evidence : Dynamic.EvidenceEnvironment}
    {environment residualEnvironment : Dynamic.Environment} {before residual : Dynamic.Heap}
    {mapping : LocationMap} {native : Resolved.Environment} {store : Core.Store} {expected : Core.Ty}
    (typed : Resolved.HasType scope result.resolved expected)
    (ledger : context.solvedRequirements = solved)
    (valid : UsedValid context solved result.consumedRequirements)
    (stagedRep : EnvironmentRep staged environment before)
    (runtimeRep : RuntimeEnvironmentRep native environment before)
    (typedEnv : RuntimeEnvironmentTyped scope native) (sameIds : native.ids = scope.ids)
    (heaps : HeapRel mapping before residual)
    (mixed : MixedEnvironment mapping before environment residualEnvironment staged) :
    ∃ final after added sourceValue nativeValue,
      Dynamic.StatementsExecute program context evidence source environment before roots final (.returned sourceValue) after ∧
      Resolved.Evaluates native store result.resolved nativeValue store ∧
      ScalarRep sourceValue nativeValue ∧ ScalarTyped nativeValue expected ∧
      SourceStagedIntegerStatementsMeaning.Extends before after added ∧
      HeapRel (mapping ++ List.replicate added.length none) after residual := by
  induction formed generalizing environment before mapping with
  | @letValue staged fuel statement rest node binder initializer initial result context next found form unit scopeFresh environmentFresh owned mono binderType initialChecked bodyChecked extension bodyFormed ih =>
    have initialValid : UsedValid context solved initial.consumedRequirements := valid.mono (by
      intro id member; exact List.mem_append_left _ member)
    have evaluated := (SourceStagedClosedEvaluationMeaning.checked_meaning (program := program)
      (evidence := evidence) ledger stagedRep fuel).1 initialChecked initialValid
    let location : Dynamic.Location := ⟨before.cells.length⟩
    let middle : Dynamic.Heap := ⟨before.cells ++ [SourceStagedIntegerStatementsMeaning.integerCell initial.value]⟩
    let nextEnvironment : Dynamic.Environment := (binder.id, location) :: environment
    have allocation : Dynamic.Heap.Allocates before .integer (some (.integer initial.value)) location middle := .append
    have binding : Dynamic.Binds environment before (bindingId (Staged.Statements.bind binder initial.value)) .integer
        (some (.integer (bindingValue (Staged.Statements.bind binder initial.value)))) nextEnvironment middle := by
      simpa only [bindingId, bindingValue, Staged.Statements.bind] using Dynamic.Binds.intro allocation
    have nextStaged := EnvironmentRep.bind (Staged.Statements.bind binder initial.value) stagedRep binding
    have nextRuntime := runtimeRep.bind sameIds binder scopeFresh allocation
    have nextMixed := mixed.erase_allocated heaps (Staged.Statements.bind binder initial.value) allocation
    have nextHeaps := heaps.erase_allocated allocation
    have nextLedger := extension.context_fields.2.2.2.2.trans ledger
    have nextValid := usedValid_extend extension (valid.mono (by intro id member; exact List.mem_append_right _ member))
    obtain ⟨final, after, added, sourceValue, nativeValue, bodyEval, nativeEval, scalar, scalarTyped, cells, heapResult⟩ :=
      ih typed nextLedger nextValid nextStaged nextRuntime nextHeaps nextMixed
    have actualAllocation : Dynamic.Heap.Allocates before binder.scheme.body (some (.integer initial.value)) location middle := by
      rw [binderType]; exact allocation
    have headEval : Dynamic.StatementExecutes program context evidence source environment before statement next
        (.fallthrough nextEnvironment) middle :=
      .letInitialized (lookupStatement?_sound found) form evaluated mono extension actualAllocation
    refine ⟨final, after, initial.value :: added, sourceValue, nativeValue, .cons headEval bodyEval,
      nativeEval, scalar, scalarTyped, ?_, ?_⟩
    · exact ((SourceStagedIntegerStatementsMeaning.Extends.refl before).allocate allocation).trans cells
    · simpa only [List.length_cons, List.replicate_succ, List.append_assoc, List.singleton_append] using heapResult
  | returnValue found form valueChecked =>
    obtain ⟨sourceValue, nativeValue, sourceEval, nativeEval, scalar, scalarTyped⟩ :=
      expression_meaning valueChecked typed ledger valid stagedRep runtimeRep typedEnv
    refine ⟨_, before, [], sourceValue, nativeValue,
      .terminal (.returnValue (lookupStatement?_sound found) form sourceEval) (.returned _),
      nativeEval, scalar, scalarTyped, .refl before, ?_⟩
    simpa using heaps
  | @conditional staged fuel statement node condition yes no guard left right context found form conditionChecked thenChecked elseChecked thenFormed elseFormed ihYes ihNo =>
    cases typed with
    | ifE guardTyped yesTyped noTyped =>
      have guardValid := valid.mono (by intro id member; exact List.mem_append_left _ (List.mem_append_left _ member))
      have yesValid := valid.mono (by intro id member; exact List.mem_append_left _ (List.mem_append_right _ member))
      have noValid := valid.mono (by intro id member; exact List.mem_append_right _ member)
      obtain ⟨guardSource, guardNative, sourceGuard, nativeGuard, scalarGuard, typedGuard⟩ :=
        expression_meaning conditionChecked guardTyped ledger guardValid stagedRep runtimeRep typedEnv
      cases typedGuard with
      | bool truth =>
        cases scalarGuard
        cases truth with
        | false =>
          obtain ⟨final, after, added, sourceValue, nativeValue, sourceEval, nativeEval, scalar, scalarTyped, cells, heapResult⟩ :=
            ihNo noTyped ledger noValid stagedRep runtimeRep heaps mixed
          have headEval := Dynamic.StatementExecutes.ifFalseWithElse (lookupStatement?_sound found) form sourceGuard sourceEval
          refine ⟨context, after, added, sourceValue, nativeValue, ?_, .ifFalse nativeGuard nativeEval,
            scalar, scalarTyped, cells, heapResult⟩
          simpa only [Dynamic.restoreControl] using Dynamic.StatementsExecute.terminal headEval (.returned _)
        | true =>
          obtain ⟨final, after, added, sourceValue, nativeValue, sourceEval, nativeEval, scalar, scalarTyped, cells, heapResult⟩ :=
            ihYes yesTyped ledger yesValid stagedRep runtimeRep heaps mixed
          have headEval := Dynamic.StatementExecutes.ifTrue (lookupStatement?_sound found) form sourceGuard sourceEval
          refine ⟨context, after, added, sourceValue, nativeValue, ?_, .ifTrue nativeGuard nativeEval,
            scalar, scalarTyped, cells, heapResult⟩
          simpa only [Dynamic.restoreControl] using Dynamic.StatementsExecute.terminal headEval (.returned _)
  | @block staged fuel statement node body result context found form bodyChecked bodyFormed ih =>
    obtain ⟨final, after, added, sourceValue, nativeValue, sourceEval, nativeEval, scalar, scalarTyped, cells, heapResult⟩ :=
      ih typed ledger valid stagedRep runtimeRep heaps mixed
    have headEval := Dynamic.StatementExecutes.block (lookupStatement?_sound found) form sourceEval
    refine ⟨context, after, added, sourceValue, nativeValue, ?_, nativeEval, scalar, scalarTyped, cells, heapResult⟩
    simpa only [Dynamic.restoreControl] using Dynamic.StatementsExecute.terminal headEval (.returned _)

end Solcore.SourceSemantics.CoreLowering.SourceStagedIntegerResidualMeaning

namespace Solcore.SourceSemantics.CoreLowering.SourceStagedIntegerResidualMeaning
open Solcore Frontend SourceInference SourceSemantics SourceCoreElaboration
open SourceCoreElaboration.Internal SourceStagedClosedEvaluationMeaning SourceStagingHeapRelation

/-- Exact original statement identities in their source order. -/
def statementRoots (source : TypedSource) : List StatementId :=
  source.roots.filterMap fun root => match root with
    | .statement statement => some statement | .expression _ => none

private theorem roots_eq {source : TypedSource} {roots : List StatementId}
    (same : roots.map NodeId.statement = source.roots) : statementRoots source = roots := by
  unfold statementRoots
  rw [← same]
  clear same
  induction roots with
  | nil => rfl
  | cons head tail ih => simpa using congrArg (List.cons head) ih

/-- Actual default acceptance and independent typing close the statement proof.
Only its static finite syntax test is an additional compiler-side condition. -/
theorem statements_of_accepted {solved : List SolvedRequirement} {source : TypedSource}
    {scope : Resolved.Context} {staged : Staged.Environment} {fuel : Nat}
    {roots : List StatementId} {result : LoweredExpression} {expected : Core.Ty}
    {site : ErrorSite} {reason : ErrorReason} {control : ControlContext} {facts : BodyFacts}
    {context finalTyped : SourceSemantics.Context}
    {program : Program} {evidence : Dynamic.EvidenceEnvironment}
    {environment residualEnvironment : Dynamic.Environment} {before residual : Dynamic.Heap}
    {mapping : LocationMap} {native : Resolved.Environment} {store : Core.Store}
    (supported : Staged.Residual.statementsSupported source fuel roots = true)
    (accepted : Staged.IntegerLet.lower solved source scope staged fuel expected site reason roots = .ok result)
    (unique : NodeOccurrencesUnique source)
    (sourceTyped : StatementsHaveType source control context roots finalTyped facts)
    (typed : Resolved.HasType scope result.resolved expected)
    (ledger : context.solvedRequirements = solved)
    (valid : UsedValid context solved result.consumedRequirements)
    (stagedRep : EnvironmentRep staged environment before)
    (runtimeRep : RuntimeEnvironmentRep native environment before)
    (typedEnv : RuntimeEnvironmentTyped scope native) (sameIds : native.ids = scope.ids)
    (heaps : HeapRel mapping before residual)
    (mixed : MixedEnvironment mapping before environment residualEnvironment staged) :
    ∃ final after added sourceValue nativeValue,
      Dynamic.StatementsExecute program context evidence source environment before roots final (.returned sourceValue) after ∧
      Resolved.Evaluates native store result.resolved nativeValue store ∧
      ScalarRep sourceValue nativeValue ∧ ScalarTyped nativeValue expected ∧
      SourceStagedIntegerStatementsMeaning.Extends before after added ∧
      HeapRel (mapping ++ List.replicate added.length none) after residual :=
  formed_meaning (bindingsFormed_of_typing (Staged.Residual.statements_checked supported accepted) unique sourceTyped)
    typed ledger valid stagedRep runtimeRep typedEnv sameIds heaps mixed

/-- The actual compatibility elaborator and its finalized artifact have the
same scalar result. Source input allocations remain in a logical residual
Source heap, selected Integer lets are omitted there, and the actual pure Core
code preserves its separate input store. This is not a statement about the
public unified compiler's callable entry or its physical Source-cell ABI. -/
theorem elaborateFunction_at_allocations {function : CheckedFunction} {artifact : ElaboratedFunction}
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {facts : BodyFacts} {arguments : List Dynamic.Value} {nativeArguments : List Core.Value}
    {initial residualInitial environment residualEnvironment : Dynamic.Environment}
    {before residualBefore bound residualBound : Dynamic.Heap} {mapping : LocationMap} {store : Core.Store}
    (accepted : elaborateFunction function = .ok artifact)
    (supported : Staged.Residual.statementsSupported function.typedBody (function.typedBody.nodes.length + 1)
      (statementRoots function.typedBody) = true)
    (unique : NodeOccurrencesUnique function.typedBody)
    (sourceTyped : BodyHasType function.typedBody context function.inferredBodyType facts)
    (ledger : context.solvedRequirements = function.solvedRequirements)
    (valid : UsedValid context function.solvedRequirements (function.solvedRequirements.map (·.id)))
    (argumentsTyped : Dynamic.ValuesHaveTypes context before arguments
      (function.typedBody.inputs.map (fun binder => binder.scheme.body)))
    (scalarArguments : ScalarValuesRep arguments nativeArguments)
    (allocated : Dynamic.BindersAllocate initial before function.typedBody.inputs arguments environment bound)
    (residualAllocated : Dynamic.BindersAllocate residualInitial residualBefore function.typedBody.inputs
      arguments residualEnvironment residualBound)
    (initialHeaps : HeapRel mapping before residualBefore)
    (initialEnvironments : EnvironmentRel mapping initial residualInitial) :
    ∃ inputMap final after added sourceValue nativeValue,
      HeapRel inputMap bound residualBound ∧ MixedEnvironment inputMap bound environment residualEnvironment [] ∧
      Dynamic.StatementsExecute program context evidence function.typedBody environment bound
        (statementRoots function.typedBody) final (.returned sourceValue) after ∧
      Resolved.Evaluates (inputEnvironment function.typedBody.inputs nativeArguments) store artifact.resolved nativeValue store ∧
      Core.Evaluates nativeArguments store artifact.core nativeValue store ∧
      ScalarRep sourceValue nativeValue ∧ ScalarTyped nativeValue artifact.returnType ∧
      SourceStagedIntegerStatementsMeaning.Extends bound after added ∧
      HeapRel (inputMap ++ List.replicate added.length none) after residualBound := by
  obtain ⟨draft, lowered, finalized⟩ := Staged.Residual.elaborated_body accepted
  obtain ⟨_, artifactInputs, artifactResolved, artifactReturn, _⟩ := Staged.Residual.finalized_fields finalized
  cases Staged.IntegerLet.function_of_accepted lowered with
  | intro owned rootsAccepted rootsSame nonempty inputsAccepted expectedAccepted bodyAccepted reconciled declaration inputEq resolved returnType rootOccurrence =>
    rename_i roots head tail inputs expected body
    have rootsSame' := roots_eq rootsSame
    have inputsChecked := Staged.Residual.inputs_checked inputsAccepted
    have sameIds := input_environment_ids allocated scalarArguments inputsChecked
    have typedEnv := inputs_typed inputsChecked argumentsTyped scalarArguments
    have runtimeRep : RuntimeEnvironmentRep (inputEnvironment function.typedBody.inputs nativeArguments) environment bound :=
      fun _ _ found => allocated_native_lookup allocated (inputs_unique_aux inputsChecked).1 scalarArguments found
    have stagedRep : EnvironmentRep [] environment bound := by intro id binding found; cases found
    obtain ⟨inputMap, inputHeaps, inputEnvironments⟩ := inputs_heaps initialHeaps
      (MixedEnvironment.of_retained initialEnvironments) allocated residualAllocated scalarArguments
    have typed := artifact_typed artifact
    rw [artifactInputs, inputEq, artifactResolved, resolved, artifactReturn, returnType] at typed
    obtain ⟨finalTyped, bodyTyped, _, _⟩ := sourceTyped
    change StatementsHaveType function.typedBody _ context (statementRoots function.typedBody) _ _ at bodyTyped
    rw [rootsSame'] at bodyTyped supported
    have used : UsedValid context function.solvedRequirements body.consumedRequirements := by
      intro row proof member consumed actual
      exact valid row proof member (List.mem_map.mpr ⟨row, member, rfl⟩) actual
    obtain ⟨final, after, added, sourceValue, nativeValue, sourceEval, nativeEval, scalar, scalarTyped, cells, heapResult⟩ :=
      statements_of_accepted supported bodyAccepted unique bodyTyped typed ledger used stagedRep runtimeRep typedEnv sameIds inputHeaps inputEnvironments
    have actualNative : Resolved.Evaluates (inputEnvironment function.typedBody.inputs nativeArguments)
        store artifact.resolved nativeValue store := by
      rw [artifactResolved, resolved]
      exact nativeEval
    have actualLowered := Resolved.Expr.lower?_sound artifact.resolvedLowered
    have loweringIds : (inputEnvironment function.typedBody.inputs nativeArguments).ids = artifact.inputs.ids := by
      rw [artifactInputs, inputEq]
      exact sameIds
    rw [← loweringIds] at actualLowered
    have core := actualNative.toCore actualLowered
    have arity := (allocation_length allocated).trans scalarArguments.length_eq
    have valueIds : (inputEnvironment function.typedBody.inputs nativeArguments).values = nativeArguments := by
      apply List.map_snd_zip
      simpa only [List.length_map] using Nat.le_of_eq arity.symm
    rw [valueIds] at core
    refine ⟨inputMap, final, after, added, sourceValue, nativeValue, inputHeaps, inputEnvironments,
      ?_, actualNative, core, scalar, ?_, cells, heapResult⟩
    · rwa [rootsSame']
    · rwa [artifactReturn, returnType]

end Solcore.SourceSemantics.CoreLowering.SourceStagedIntegerResidualMeaning

namespace Solcore.SourceSemantics.CoreLowering.SourceStagedIntegerResidualMeaning
open Solcore Frontend SourceInference SourceSemantics SourceCoreElaboration
open SourceCoreElaboration.Internal SourceStagedClosedEvaluationMeaning SourceStagingHeapRelation

/-- Construct the original ordered parameter allocation from its exact arity.
All initial cells and lexical entries remain in the actual allocation trace. -/
theorem allocate_inputs (inputs : List TypedBinder) (values : List Dynamic.Value)
    (arity : inputs.length = values.length) (initial : Dynamic.Environment) (before : Dynamic.Heap) :
    ∃ environment after, Dynamic.BindersAllocate initial before inputs values environment after := by
  induction inputs generalizing values initial before with
  | nil =>
    cases values with
    | nil => exact ⟨initial, before, .nil _ _⟩
    | cons head tail => simp at arity
  | cons binder rest ih =>
    cases values with
    | nil => simp at arity
    | cons value values =>
      let location : Dynamic.Location := ⟨before.cells.length⟩
      let middle : Dynamic.Heap := ⟨before.cells ++ [{type := binder.scheme.body, value := some value}]⟩
      have allocation : Dynamic.Heap.Allocates before binder.scheme.body (some value) location middle := .append
      obtain ⟨environment, after, tail⟩ := ih values (Nat.succ.inj arity) ((binder.id, location) :: initial) middle
      exact ⟨environment, after, .cons allocation tail⟩

/-- Public accepted elaboration constructs both actual ordered Source input
allocations before using the closed body theorem. Runtime scalar cells are
kept; only selected Integer lets are omitted from the logical residual heap.
The resulting Core expression uses the unchanged independent pure store. -/
theorem elaborateFunction_sound {function : CheckedFunction} {artifact : ElaboratedFunction}
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {facts : BodyFacts} {arguments : List Dynamic.Value} {nativeArguments : List Core.Value}
    {initial residualInitial : Dynamic.Environment} {before residualBefore : Dynamic.Heap}
    {mapping : LocationMap} {store : Core.Store}
    (accepted : elaborateFunction function = .ok artifact)
    (supported : Staged.Residual.statementsSupported function.typedBody (function.typedBody.nodes.length + 1)
      (statementRoots function.typedBody) = true)
    (unique : NodeOccurrencesUnique function.typedBody)
    (sourceTyped : BodyHasType function.typedBody context function.inferredBodyType facts)
    (ledger : context.solvedRequirements = function.solvedRequirements)
    (valid : UsedValid context function.solvedRequirements (function.solvedRequirements.map (·.id)))
    (argumentsTyped : Dynamic.ValuesHaveTypes context before arguments
      (function.typedBody.inputs.map (fun binder => binder.scheme.body)))
    (scalarArguments : ScalarValuesRep arguments nativeArguments)
    (initialHeaps : HeapRel mapping before residualBefore)
    (initialEnvironments : EnvironmentRel mapping initial residualInitial) :
    ∃ environment bound residualEnvironment residualBound inputMap final after added sourceValue nativeValue,
      Dynamic.BindersAllocate initial before function.typedBody.inputs arguments environment bound ∧
      Dynamic.BindersAllocate residualInitial residualBefore function.typedBody.inputs arguments residualEnvironment residualBound ∧
      HeapRel inputMap bound residualBound ∧ MixedEnvironment inputMap bound environment residualEnvironment [] ∧
      Dynamic.StatementsExecute program context evidence function.typedBody environment bound
        (statementRoots function.typedBody) final (.returned sourceValue) after ∧
      Resolved.Evaluates (inputEnvironment function.typedBody.inputs nativeArguments) store artifact.resolved nativeValue store ∧
      Core.Evaluates nativeArguments store artifact.core nativeValue store ∧
      ScalarRep sourceValue nativeValue ∧ ScalarTyped nativeValue artifact.returnType ∧
      SourceStagedIntegerStatementsMeaning.Extends bound after added ∧
      HeapRel (inputMap ++ List.replicate added.length none) after residualBound := by
  have arity : function.typedBody.inputs.length = arguments.length := by
    simpa only [List.length_map] using argumentsTyped.length_eq.symm
  obtain ⟨environment, bound, allocated⟩ := allocate_inputs function.typedBody.inputs arguments arity initial before
  obtain ⟨residualEnvironment, residualBound, residualAllocated⟩ :=
    allocate_inputs function.typedBody.inputs arguments arity residualInitial residualBefore
  obtain ⟨inputMap, final, after, added, sourceValue, nativeValue, meaning⟩ :=
    elaborateFunction_at_allocations accepted supported unique sourceTyped ledger valid argumentsTyped scalarArguments
      allocated residualAllocated initialHeaps initialEnvironments
  exact ⟨environment, bound, residualEnvironment, residualBound, inputMap, final, after, added, sourceValue, nativeValue,
    allocated, residualAllocated, meaning⟩

end Solcore.SourceSemantics.CoreLowering.SourceStagedIntegerResidualMeaning

set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.SourceStagedIntegerResidualMeaning
open Solcore Frontend SourceInference SourceSemantics SourceCoreElaboration
open SourceCoreElaboration.Internal SourceStagedClosedEvaluationMeaning SourceStagingHeapRelation

/-- An original Core completion identifies the value and complete Core store
of the accepted scalar artifact. Both Source input allocations and the complete
logical residual heap relation remain those of the closed Source witness. -/
theorem elaborateFunction_reflects {function : CheckedFunction} {artifact : ElaboratedFunction}
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {facts : BodyFacts} {arguments : List Dynamic.Value} {nativeArguments : List Core.Value}
    {initial residualInitial : Dynamic.Environment} {before residualBefore : Dynamic.Heap}
    {mapping : LocationMap} {store finalStore : Core.Store} {value : Core.Value}
    (accepted : elaborateFunction function = .ok artifact)
    (supported : Staged.Residual.statementsSupported function.typedBody (function.typedBody.nodes.length + 1)
      (statementRoots function.typedBody) = true)
    (unique : NodeOccurrencesUnique function.typedBody)
    (sourceTyped : BodyHasType function.typedBody context function.inferredBodyType facts)
    (ledger : context.solvedRequirements = function.solvedRequirements)
    (valid : UsedValid context function.solvedRequirements (function.solvedRequirements.map (·.id)))
    (argumentsTyped : Dynamic.ValuesHaveTypes context before arguments
      (function.typedBody.inputs.map (fun binder => binder.scheme.body)))
    (scalarArguments : ScalarValuesRep arguments nativeArguments)
    (initialHeaps : HeapRel mapping before residualBefore)
    (initialEnvironments : EnvironmentRel mapping initial residualInitial)
    (completed : Core.Evaluates nativeArguments store artifact.core value finalStore) :
    finalStore = store ∧
    ∃ environment bound residualEnvironment residualBound inputMap final after added sourceValue,
      Dynamic.BindersAllocate initial before function.typedBody.inputs arguments environment bound ∧
      Dynamic.BindersAllocate residualInitial residualBefore function.typedBody.inputs arguments residualEnvironment residualBound ∧
      HeapRel inputMap bound residualBound ∧ MixedEnvironment inputMap bound environment residualEnvironment [] ∧
      Dynamic.StatementsExecute program context evidence function.typedBody environment bound
        (statementRoots function.typedBody) final (.returned sourceValue) after ∧
      Resolved.Evaluates (inputEnvironment function.typedBody.inputs nativeArguments) store artifact.resolved value store ∧
      ScalarRep sourceValue value ∧ ScalarTyped value artifact.returnType ∧
      SourceStagedIntegerStatementsMeaning.Extends bound after added ∧
      HeapRel (inputMap ++ List.replicate added.length none) after residualBound := by
  obtain ⟨environment, bound, residualEnvironment, residualBound, inputMap, final, after, added,
    sourceValue, expectedValue, allocated, residualAllocated, inputHeaps, inputEnvironments,
    sourceEvaluation, residualEvaluation, coreEvaluation, represented, typed, suffix, finalHeaps⟩ :=
    elaborateFunction_sound accepted supported unique sourceTyped ledger valid argumentsTyped scalarArguments initialHeaps initialEnvironments
  obtain ⟨rfl, rfl⟩ := Core.evaluation_deterministic completed coreEvaluation
  exact ⟨rfl, environment, bound, residualEnvironment, residualBound, inputMap, final, after, added,
    sourceValue, allocated, residualAllocated, inputHeaps, inputEnvironments,
    sourceEvaluation, residualEvaluation, represented, typed, suffix, finalHeaps⟩

/-- Finite completion of the actual initial machine state supplies the original
Core derivation. The pure Core store remains separate from the Source heaps. -/
theorem elaborateFunction_runStateful_reflects {function : CheckedFunction} {artifact : ElaboratedFunction}
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {facts : BodyFacts} {arguments : List Dynamic.Value} {nativeArguments : List Core.Value}
    {initial residualInitial : Dynamic.Environment} {before residualBefore : Dynamic.Heap}
    {mapping : LocationMap} {store finalStore : Core.Store} {value : Core.Value} {fuel : Nat}
    (accepted : elaborateFunction function = .ok artifact)
    (supported : Staged.Residual.statementsSupported function.typedBody (function.typedBody.nodes.length + 1)
      (statementRoots function.typedBody) = true)
    (unique : NodeOccurrencesUnique function.typedBody)
    (sourceTyped : BodyHasType function.typedBody context function.inferredBodyType facts)
    (ledger : context.solvedRequirements = function.solvedRequirements)
    (valid : UsedValid context function.solvedRequirements (function.solvedRequirements.map (·.id)))
    (argumentsTyped : Dynamic.ValuesHaveTypes context before arguments
      (function.typedBody.inputs.map (fun binder => binder.scheme.body)))
    (scalarArguments : ScalarValuesRep arguments nativeArguments)
    (initialHeaps : HeapRel mapping before residualBefore)
    (initialEnvironments : EnvironmentRel mapping initial residualInitial)
    (completed : Core.runStateful fuel (Core.State.initial artifact.core nativeArguments store) =
      .done value finalStore) :
    finalStore = store ∧
    ∃ environment bound residualEnvironment residualBound inputMap final after added sourceValue,
      Dynamic.BindersAllocate initial before function.typedBody.inputs arguments environment bound ∧
      Dynamic.BindersAllocate residualInitial residualBefore function.typedBody.inputs arguments residualEnvironment residualBound ∧
      HeapRel inputMap bound residualBound ∧ MixedEnvironment inputMap bound environment residualEnvironment [] ∧
      Dynamic.StatementsExecute program context evidence function.typedBody environment bound
        (statementRoots function.typedBody) final (.returned sourceValue) after ∧
      Resolved.Evaluates (inputEnvironment function.typedBody.inputs nativeArguments) store artifact.resolved value store ∧
      ScalarRep sourceValue value ∧ ScalarTyped value artifact.returnType ∧
      SourceStagedIntegerStatementsMeaning.Extends bound after added ∧
      HeapRel (inputMap ++ List.replicate added.length none) after residualBound :=
  elaborateFunction_reflects accepted supported unique sourceTyped ledger valid argumentsTyped scalarArguments initialHeaps initialEnvironments
    (Core.runStateful_evaluation_sound completed)

end Solcore.SourceSemantics.CoreLowering.SourceStagedIntegerResidualMeaning
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SourceAuthenticatedReferenceOrigin
/-! The actual authenticator identifies the same original caller and read
before its contextual substitution. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
namespace Solcore.SourceSemantics.CoreLowering.SourceAuthenticatedReferenceOrigin
open Frontend SourceInference TypeSystem SourceCoreLocalEvidence
open CallableBodyMetadataViews

private theorem bind_ok {α β ε : Type} {action : Except ε α}
    {next : α → Except ε β} {output : β} (accepted : action >>= next = .ok output) :
    ∃ value, action = .ok value ∧ next value = .ok output := by
  cases action with
  | error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

open Lean Meta Elab Tactic in
private def unfoldCheck (hypothesis : Name) : TacticM Unit := withMainContext do
  let declaration ← getLocalDeclFromUserName hypothesis
  let type ← instantiateMVars (← inferType declaration.toExpr)
  let some (_, left, _) := type.eq? | throwError "expected equation: {type}"
  let .const name _ := left.getAppFn | throwError "expected actual definition: {left}"
  let goal ← getMainGoal
  replaceMainGoal [← unfoldLocalDecl goal declaration.fvarId name]

private theorem exact_caller {plan : SourceSpecializationWorklist.Plan}
    {binding : Binding} {caller : SourceSpecialization.SpecializedFunction}
    (accepted : exactCaller plan binding = .ok caller) :
    SourceCompilationPlan.exactSpecialization plan binding.caller = .ok caller ∧
      caller.function.typedBody = binding.source := by
  unfold exactCaller at accepted
  obtain ⟨original, selected, accepted⟩ := bind_ok accepted
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at accepted
  split at accepted <;> try contradiction
  rename_i sourceEq
  split at accepted <;> try contradiction
  cases accepted
  have selected : SourceCompilationPlan.exactSpecialization plan binding.caller = .ok caller := by
    cases actual : SourceCompilationPlan.exactSpecialization plan binding.caller with
    | error error => simp only [actual, Except.mapError, reduceCtorEq] at selected
    | ok result => simpa only [actual, Except.mapError, Except.ok.injEq] using selected
  exact ⟨selected, by simpa using sourceEq⟩

/-- Authentication checks a declaration with the complete binding metadata,
including its initializer, in the original source. -/
theorem binding_retained
    {program : CheckedProgram} {plan : SourceSpecializationWorklist.Plan}
    {binding : Binding} {parent : Option Prepared} {id : ExpressionId}
    {reference : Reference}
    (accepted : authenticateReference program plan binding parent id = .ok reference) :
    ∃ statement, Node.statement statement ∈ binding.source.nodes ∧
      statement.form = .letDecl binding.binder (some binding.initializer) := by
  unfold authenticateReference at accepted
  obtain ⟨caller, callerAccepted, _⟩ := bind_ok accepted
  unfold exactCaller at callerAccepted
  obtain ⟨original, _selected, callerAccepted⟩ := bind_ok callerAccepted
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe,
    MonadExceptOf.throw] at callerAccepted
  split at callerAccepted <;> try contradiction
  split at callerAccepted <;> try contradiction
  rename_i retained
  obtain ⟨node, present, matched⟩ := List.any_eq_true.mp retained
  cases node with
  | expression expression => cases matched
  | statement statement =>
    cases statement with
    | mk sid span type form =>
      cases form <;> try cases matched
      next binder initializer =>
        cases initializer with
        | none => cases matched
        | some initializer =>
          have identities : binder = binding.binder ∧ initializer = binding.initializer :=
            of_decide_eq_true matched
          rcases identities with ⟨rfl, rfl⟩
          exact ⟨_, present, rfl⟩

/-- The original read and its caller are recovered from the real factory;
only its types and metadata are substituted in the contextual reference. -/
theorem original_lookup
    {program : CheckedProgram} {plan : SourceSpecializationWorklist.Plan}
    {binding : Binding} {parent : Option Prepared} {id : ExpressionId}
    {reference : Reference}
    (accepted : authenticateReference program plan binding parent id = .ok reference) :
    ∃ caller original name,
      SourceCompilationPlan.exactSpecialization plan binding.caller = .ok caller ∧
      caller.function.typedBody = binding.source ∧
      binding.source.lookupExpression? id = some original ∧
      reference.original = original.applySubstitution ((parent.map (·.substitution)).getD []) ∧
      original.form = .reference name (.local binding.binder.id) := by
  unfold authenticateReference at accepted
  obtain ⟨caller, callerAccepted, accepted⟩ := bind_ok accepted
  obtain ⟨⟨active, inherited⟩, contextAccepted, accepted⟩ := bind_ok accepted
  obtain ⟨validated, _validated, accepted⟩ := bind_ok accepted
  cases validated
  have callerFacts := exact_caller callerAccepted
  have activeEq : active = ((parent.map (·.substitution)).getD []) := by
    run_tac unfoldCheck `contextAccepted
    cases parent with
    | none => cases contextAccepted; rfl
    | some parent =>
      simp only at contextAccepted
      split at contextAccepted <;> try contradiction
      cases contextAccepted
      rfl
  dsimp only at accepted
  split at accepted
  · next node found =>
    simp only [bind, Except.bind, pure, Except.pure, throw, throwThe,
      MonadExceptOf.throw] at accepted
    split at accepted
    · cases accepted
    · split at accepted
      · next name localId form =>
        split at accepted
        · cases accepted
        · next same =>
          split at accepted
          · next owned ownedEq =>
            obtain ⟨available, _available, accepted⟩ := bind_ok accepted
            obtain ⟨⟨child, witnesses⟩, _factory, accepted⟩ := bind_ok accepted
            obtain ⟨validated, _witnesses, accepted⟩ := bind_ok accepted
            cases validated
            cases accepted
            change (caller.function.typedBody.applySubstitution active).lookupExpression? id = some node at found
            rw [callerFacts.2, lookupExpression_apply] at found
            cases before : binding.source.lookupExpression? id with
            | none => simp only [before, Option.map_none, reduceCtorEq] at found
            | some original =>
              have nodeEq : original.applySubstitution active = node := by
                simpa only [before, Option.map_some, Option.some.injEq] using found
              have localEq : localId = binding.binder.id := by simpa using same
              refine ⟨caller, original, name, callerFacts.1, callerFacts.2, rfl, ?_, ?_⟩
              · exact nodeEq.symm.trans (congrArg (original.applySubstitution) activeEq)
              · rw [← nodeEq, localEq] at form
                cases original with
                | mk id span type actual requirements coercions localStart =>
                  cases actual <;>
                    simp only [ExpressionNode.applySubstitution, ExpressionForm.applySubstitution,
                      reduceCtorEq] at form
                  next originalName resolution =>
                    cases resolution <;> simp only [ReferenceResolution.applySubstitution] at form <;>
                      cases form <;> rfl
          · cases accepted
      · cases accepted
  · cases accepted

/-- A prepared view keeps the original declaration read selected by its actual
authentication, before the parent substitution. -/
theorem view_original_lookup
    {program : CheckedProgram} {plan : SourceSpecializationWorklist.Plan}
    (view : SourceCoreCallableViews.View program plan) :
    ∃ caller original name,
      SourceCompilationPlan.exactSpecialization plan view.owner = .ok caller ∧
      caller.function.typedBody = view.binding.source ∧
      view.binding.source.lookupExpression? view.read = some original ∧
      view.reference.original = original.applySubstitution view.parentActive ∧
      original.form = .reference name (.local view.binding.binder.id) := by
  exact original_lookup view.authenticatedReference

end Solcore.SourceSemantics.CoreLowering.SourceAuthenticatedReferenceOrigin
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ResidualScopeReachability
/-! Canonical source-reference paths extend the validator's actual residual
scope. The suffix keeps its starting scope, so variables introduced by nested
declarations can be distinguished from variables captured at body entry. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.ResidualScopeReachability
open Frontend SourceInference TypeSystem SourceSpecialization SourceSpecializationWorklist
open CallableLambdaBodyReachability

private theorem expression_node {source : TypedSource} {id : ExpressionId} {node : ExpressionNode}
    (found : source.lookupExpression? id = some node) :
    source.lookupNode? id.occurrence = some (.expression node) := by
  unfold TypedSource.lookupExpression? at found
  cases selected : source.lookupNode? id.occurrence with
  | none => simp [selected] at found
  | some actual =>
    cases actual with
    | statement => simp [selected] at found
    | expression expression =>
      have same : expression = node := by simpa [selected] using found
      simp only [same]

private theorem statement_node {source : TypedSource} {id : StatementId} {node : StatementNode}
    (found : source.lookupStatement? id = some node) :
    source.lookupNode? id.occurrence = some (.statement node) := by
  unfold TypedSource.lookupStatement? at found
  cases selected : source.lookupNode? id.occurrence with
  | none => simp [selected] at found
  | some actual =>
    cases actual with
    | expression => simp [selected] at found
    | statement statement =>
      have same : statement = node := by simpa [selected] using found
      simp only [same]

private theorem scheduled_expression {source : TypedSource} {id : ExpressionId}
    {node : ExpressionNode} (found : source.lookupExpression? id = some node)
    {child : NodeId} (edge : child ∈ node.form.references) (variables : List TypeVarId) :
    ∃ next, (child, next) ∈ residualScopeChildren source (.expression id) variables := by
  have selected : child ∈
      (residualScopeChildren source (.expression id) variables).map Prod.fst := by
    rw [residualScopeChildren_ids]
    simpa only [NodeId.occurrenceId, expression_node found,
      expressionChildNodeIds_eq_references] using edge
  obtain ⟨pair, member, same⟩ := List.mem_map.mp selected
  exact ⟨pair.2, same ▸ member⟩

private theorem scheduled_statement {source : TypedSource} {id : StatementId}
    {node : StatementNode} (found : source.lookupStatement? id = some node)
    {child : NodeId} (edge : child ∈ node.form.references) (variables : List TypeVarId) :
    ∃ next, (child, next) ∈ residualScopeChildren source (.statement id) variables := by
  have selected : child ∈
      (residualScopeChildren source (.statement id) variables).map Prod.fst := by
    rw [residualScopeChildren_ids]
    simpa only [NodeId.occurrenceId, statement_node found] using
      statementChildNodeIds_of_reference (source := source) edge
  obtain ⟨pair, member, same⟩ := List.mem_map.mp selected
  exact ⟨pair.2, same ▸ member⟩

/-- Every real reference path from this root extends the same starting scope;
neither a global node-coverage law nor a different path is used. -/
theorem tail_of_reaches {source : TypedSource} {root node : NodeId}
    (path : Reaches source [root] node) (variables : List TypeVarId) :
    ∃ next, ResidualScopeTail source root variables node next := by
  induction path with
  | root member =>
    cases List.mem_singleton.mp member
    exact ⟨variables, .refl⟩
  | expression _ found edge ih =>
    obtain ⟨before, tail⟩ := ih
    obtain ⟨next, scheduled⟩ := scheduled_expression found edge before
    exact ⟨next, .child tail scheduled⟩
  | statement _ found edge ih =>
    obtain ⟨before, tail⟩ := ih
    obtain ⟨next, scheduled⟩ := scheduled_statement found edge before
    exact ⟨next, .child tail scheduled⟩

/-- Body execution selects one actual root. The returned evidence preserves
that root's covered entry scope and every later scheduled edge. -/
theorem covered_root_of_reaches {source : TypedSource} {roots : List NodeId}
    {domain : List TypeVarId} (covered : ResidualEntryCovered source roots domain)
    {node : NodeId} (path : Reaches source roots node) :
    ∃ root firstVariables variables,
      root ∈ roots ∧ ResidualScopePath source root firstVariables ∧
      firstVariables ⊆ domain ∧ ResidualScopeTail source root firstVariables node variables := by
  induction path with
  | @root id member =>
    obtain ⟨variables, scope, supported⟩ := covered id member
    exact ⟨id, variables, variables, member, scope, supported, .refl⟩
  | expression _ found edge ih =>
    obtain ⟨root, firstVariables, variables, member, scope, supported, tail⟩ := ih
    obtain ⟨next, scheduled⟩ := scheduled_expression found edge variables
    exact ⟨root, firstVariables, next, member, scope, supported, .child tail scheduled⟩
  | statement _ found edge ih =>
    obtain ⟨root, firstVariables, variables, member, scope, supported, tail⟩ := ih
    obtain ⟨next, scheduled⟩ := scheduled_statement found edge variables
    exact ⟨root, firstVariables, next, member, scope, supported, .child tail scheduled⟩

/-- Variables outside the covered entry were introduced by an initialized
statement on this same canonical body path. The complete statement lookup is
retained for the actual allocation-order producer. -/
theorem scope_of_reaches {source : TypedSource} {roots : List NodeId}
    {domain : List TypeVarId} (covered : ResidualEntryCovered source roots domain)
    {node : NodeId} (path : Reaches source roots node) :
    ∃ variables, ResidualScopePath source node variables ∧
      ∀ metavariable ∈ variables, metavariable ∈ domain ∨
        ∃ id statement binder initializer,
          Reaches source roots (.statement id) ∧
          source.lookupStatement? id = some statement ∧
          statement.form = .letDecl binder (some initializer) ∧
          metavariable ∈ binder.scheme.quantified := by
  induction path with
  | @root id member =>
    obtain ⟨variables, scope, supported⟩ := covered id member
    exact ⟨variables, scope, fun _ occurs => .inl (supported occurs)⟩
  | @expression id node child parent found edge ih =>
    obtain ⟨before, scope, origins⟩ := ih
    obtain ⟨variables, scheduled⟩ := scheduled_expression found edge before
    refine ⟨variables, .child scope scheduled, ?_⟩
    intro metavariable present
    by_cases old : metavariable ∈ before
    · exact origins metavariable old
    · obtain ⟨statement, binder, initializer, impossible, _, _, _⟩ :=
        residualScopeChildren_new_quantifier scheduled present old
      simp only [NodeId.occurrenceId, expression_node found] at impossible
      cases impossible
  | @statement id node child parent found edge ih =>
    obtain ⟨before, scope, origins⟩ := ih
    obtain ⟨variables, scheduled⟩ := scheduled_statement found edge before
    refine ⟨variables, .child scope scheduled, ?_⟩
    intro metavariable present
    by_cases old : metavariable ∈ before
    · exact origins metavariable old
    · obtain ⟨statement, binder, initializer, selected, form, _, owned⟩ :=
        residualScopeChildren_new_quantifier scheduled present old
      have same : statement = node :=
        Node.statement.inj (Option.some.inj (selected.symm.trans (statement_node found)))
      subst statement
      exact .inr ⟨id, node, binder, initializer, parent, found, form, owned⟩

/-- A real initialized loop item is scheduled from the retained loop
statement. That scheduler preserves its inherited residual scope. -/
theorem capture_header {source : TypedSource} {roots : List NodeId}
    {domain : List TypeVarId} (covered : ResidualEntryCovered source roots domain)
    {id : StatementId} (path : LocalLambdaLexicalPath source roots (.statement id))
    {statement : StatementNode} (found : source.lookupStatement? id = some statement)
    {initializers post : List ForItemForm} {condition : ExpressionId} {body : List StatementId}
    (form : statement.form = .forLoop initializers condition post body)
    {binder : TypedBinder} {initializer : ExpressionId}
    (member : .letDecl binder (some initializer) ∈ initializers ++ post) :
    CapturedResidualScope source initializer binder.scheme.quantified domain := by
  obtain ⟨before, scope, inherited⟩ := path.statement_scope covered
  have present : NodeId.expression initializer ∈
      (initializers ++ post).flatMap ForItemForm.references :=
    List.mem_flatMap.mpr ⟨.letDecl binder (some initializer), member,
      by simp [ForItemForm.references]⟩
  have edge : NodeId.expression initializer ∈ statement.form.references := by
    simp only [List.flatMap_append, List.mem_append] at present
    simp only [form, StatementForm.references, List.mem_append]
    exact present.elim (fun p => .inl (.inl (.inl p))) (fun p => .inl (.inr p))
  obtain ⟨variables, scheduled⟩ := scheduled_statement found edge before
  refine ⟨variables, .child scope scheduled, ?_⟩
  intro metavariable occurs
  by_cases old : metavariable ∈ before
  · exact .inr (inherited old)
  · obtain ⟨other, owner, initialized, selected, initializedForm, _, _⟩ :=
      residualScopeChildren_new_quantifier scheduled occurs old
    have same : other = statement :=
      Node.statement.inj (Option.some.inj (selected.symm.trans (statement_node found)))
    subst other
    rw [form] at initializedForm
    cases initializedForm

end Solcore.SourceSemantics.CoreLowering.ResidualScopeReachability
end
