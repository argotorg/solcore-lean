import Solcore.SourceSemantics.CoreLowering.SourceStagedIntegerStatementsMeaning
import Solcore.SourceSemantics.CoreLowering.StagedValue

set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.SourceStagingHeapRelation
open Frontend SourceInference Solcore.SourceSemantics.Dynamic TypeSystem

/-! Static bounds for every captured source location, including unused and
shadowed environment entries. These facts do not execute or rewrite code. -/
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
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ typed
  · intro location captured; cases captured
  · intro _ location captured; cases captured
  · intro _ location captured; cases captured
  · intro _ location captured; cases captured
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
