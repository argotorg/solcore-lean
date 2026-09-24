import Solcore.SourceSemantics.Dynamic.Value

/-!
Declarative environment and heap operations for source evaluation.

The relations below are structural specifications.  They do not invoke the
executable runtime's lookup, allocation, or update functions.  Environment
lookup uses first-match shadowing; heap allocation appends one fresh cell; and
heap writes preserve the selected cell's declared type.
-/

set_option autoImplicit false

namespace Solcore.SourceSemantics.Dynamic

open TypeSystem

/-- One mutable cell retains its source type even when uninitialized.  A
generalized direct-lambda cell additionally retains its principal closure so
each read can materialize a use-site-specific ordinary closure. -/
structure Cell where
  type : Ty
  value : Option Value
  generalized : Option GeneralizedClosure := none
  deriving Repr

/-- A finite source heap.  Locations are stable list indices. -/
structure Heap where
  cells : List Cell := []
  deriving Repr

namespace Environment

/-- First-match lookup in a lexical environment. -/
inductive LooksUp : Environment → Resolved.LocalId → Location → Prop where
  | head {environment id location} :
      LooksUp ((id, location) :: environment) id location
  | tail {environment id other location found}
      (different : other ≠ id)
      (rest : LooksUp environment id found) :
      LooksUp ((other, location) :: environment) id found

theorem LooksUp.functional
    {environment : Environment} {id : Resolved.LocalId}
    {left right : Location}
    (leftLookup : LooksUp environment id left)
    (rightLookup : LooksUp environment id right) :
    left = right := by
  induction leftLookup with
  | head =>
      cases rightLookup with
      | head => rfl
      | tail different _ => exact (different rfl).elim
  | tail different rest inductionHypothesis =>
      cases rightLookup with
      | head => exact (different rfl).elim
      | tail _ rightRest => exact inductionHypothesis rightRest

theorem LooksUp.ne_of_tail
    {environment : Environment} {id other : Resolved.LocalId}
    {location found : Location}
    (lookup : LooksUp ((other, location) :: environment) id found)
    (different : other ≠ id) :
    LooksUp environment id found := by
  cases lookup with
  | head => exact (different rfl).elim
  | tail _ rest => exact rest

end Environment

namespace Heap

/-- Structural selection of the cell at a natural-number index. -/
inductive CellAt : List Cell → Nat → Cell → Prop where
  | head {cell cells} : CellAt (cell :: cells) 0 cell
  | tail {cell cells index found}
      (rest : CellAt cells index found) :
      CellAt (cell :: cells) (index + 1) found

/-- Declarative heap read. -/
inductive Reads (heap : Heap) (location : Location) (cell : Cell) : Prop where
  | intro (selected : CellAt heap.cells location.index cell) :
      Reads heap location cell

/-- Structural replacement at one existing index. -/
inductive CellsWrite : List Cell → Nat → Cell → List Cell → Prop where
  | head {previous replacement rest} :
      CellsWrite (previous :: rest) 0 replacement (replacement :: rest)
  | tail {previous rest index replacement updated}
      (write : CellsWrite rest index replacement updated) :
      CellsWrite (previous :: rest) (index + 1) replacement
        (previous :: updated)

/-- Allocate one cell at the fresh final location. -/
inductive Allocates (heap : Heap) (type : Ty) (value : Option Value) :
    Location → Heap → Prop where
  | append :
      Allocates heap type value ⟨heap.cells.length⟩
        ⟨heap.cells ++ [({ type := type, value := value } : Cell)]⟩

/-- Allocate one principal generalized closure at the fresh final location.
The retained cell type is the binder's principal scheme body; no ordinary
value is materialized until a particular use site supplies an instantiation. -/
inductive AllocatesGeneralized (heap : Heap) (function : GeneralizedClosure) :
    Location → Heap → Prop where
  | append :
      AllocatesGeneralized heap function ⟨heap.cells.length⟩
        ⟨heap.cells ++ [{
          type := function.binder.scheme.body
          value := none
          generalized := some function
        }]⟩

/-- Write only the optional value of one existing cell. -/
inductive Writes (heap : Heap) (location : Location)
    (value : Option Value) : Heap → Prop where
  | intro {previous : Cell} {updated : List Cell}
      (read : Reads heap location previous)
      (write : CellsWrite heap.cells location.index
        { previous with value := value } updated) :
      Writes heap location value ⟨updated⟩

namespace CellAt

theorem functional {cells : List Cell} {index : Nat} {left right : Cell}
    (leftAt : CellAt cells index left)
    (rightAt : CellAt cells index right) :
    left = right := by
  induction leftAt with
  | head =>
      cases rightAt with
      | head => rfl
  | tail leftRest inductionHypothesis =>
      cases rightAt with
      | tail rightRest => exact inductionHypothesis rightRest

theorem index_lt_length {cells : List Cell} {index : Nat} {cell : Cell}
    (selected : CellAt cells index cell) : index < cells.length := by
  induction selected with
  | head => simp
  | tail _ inductionHypothesis => simpa using Nat.succ_lt_succ inductionHypothesis

theorem append_left {cells suffix : List Cell} {index : Nat} {cell : Cell}
    (selected : CellAt cells index cell) :
    CellAt (cells ++ suffix) index cell := by
  induction selected with
  | head => exact .head
  | tail _ inductionHypothesis => exact .tail inductionHypothesis

theorem append_last (cells : List Cell) (cell : Cell) :
    CellAt (cells ++ [cell]) cells.length cell := by
  induction cells with
  | nil => exact .head
  | cons head tail inductionHypothesis =>
      simpa using CellAt.tail inductionHypothesis

end CellAt

namespace Reads

theorem functional {heap : Heap} {location : Location} {left right : Cell}
    (leftRead : Reads heap location left)
    (rightRead : Reads heap location right) :
    left = right := by
  cases leftRead with
  | intro leftAt =>
      cases rightRead with
      | intro rightAt => exact leftAt.functional rightAt

theorem location_valid {heap : Heap} {location : Location} {cell : Cell}
    (read : Reads heap location cell) :
    location.index < heap.cells.length := by
  cases read with
  | intro selected => exact selected.index_lt_length

end Reads

namespace CellsWrite

theorem length_eq {cells updated : List Cell} {index : Nat}
    {replacement : Cell}
    (write : CellsWrite cells index replacement updated) :
    updated.length = cells.length := by
  induction write with
  | head => rfl
  | tail _ inductionHypothesis => simp [inductionHypothesis]

theorem reads_replacement {cells updated : List Cell} {index : Nat}
    {replacement : Cell}
    (write : CellsWrite cells index replacement updated) :
    CellAt updated index replacement := by
  induction write with
  | head => exact .head
  | tail _ inductionHypothesis => exact .tail inductionHypothesis

theorem preserves_other
    {cells updated : List Cell} {index other : Nat}
    {replacement selected : Cell}
    (write : CellsWrite cells index replacement updated)
    (different : other ≠ index)
    (read : CellAt cells other selected) :
    CellAt updated other selected := by
  induction write generalizing other with
  | head =>
      cases read with
      | head => exact (different rfl).elim
      | tail rest => exact .tail rest
  | tail write inductionHypothesis =>
      cases read with
      | head => exact .head
      | tail rest =>
          apply CellAt.tail
          apply inductionHypothesis
          · intro equal
            apply different
            simp [equal]
          · exact rest

end CellsWrite

namespace Allocates

theorem location_fresh
    {heap : Heap} {type : Ty} {value : Option Value}
    {location : Location} {updated : Heap}
    (allocation : Allocates heap type value location updated) :
    location.index = heap.cells.length := by
  cases allocation
  rfl

theorem length_eq_succ
    {heap : Heap} {type : Ty} {value : Option Value}
    {location : Location} {updated : Heap}
    (allocation : Allocates heap type value location updated) :
    updated.cells.length = heap.cells.length + 1 := by
  cases allocation
  simp

theorem reads_new
    {heap : Heap} {type : Ty} {value : Option Value}
    {location : Location} {updated : Heap}
    (allocation : Allocates heap type value location updated) :
    Reads updated location { type := type, value := value } := by
  cases allocation
  exact .intro (CellAt.append_last heap.cells
    { type := type, value := value })

theorem preserves_read
    {heap : Heap} {type : Ty} {value : Option Value}
    {location : Location} {updated : Heap}
    (allocation : Allocates heap type value location updated)
    {oldLocation : Location} {cell : Cell}
    (read : Reads heap oldLocation cell) :
    Reads updated oldLocation cell := by
  cases allocation
  cases read with
  | intro selected => exact .intro selected.append_left

end Allocates

namespace AllocatesGeneralized

theorem location_fresh
    {heap : Heap} {function : GeneralizedClosure}
    {location : Location} {updated : Heap}
    (allocation : AllocatesGeneralized heap function location updated) :
    location.index = heap.cells.length := by
  cases allocation
  rfl

theorem length_eq_succ
    {heap : Heap} {function : GeneralizedClosure}
    {location : Location} {updated : Heap}
    (allocation : AllocatesGeneralized heap function location updated) :
    updated.cells.length = heap.cells.length + 1 := by
  cases allocation
  simp

theorem reads_new
    {heap : Heap} {function : GeneralizedClosure}
    {location : Location} {updated : Heap}
    (allocation : AllocatesGeneralized heap function location updated) :
    Reads updated location {
      type := function.binder.scheme.body
      value := none
      generalized := some function
    } := by
  cases allocation
  exact .intro (CellAt.append_last heap.cells {
    type := function.binder.scheme.body
    value := none
    generalized := some function
  })

theorem preserves_read
    {heap : Heap} {function : GeneralizedClosure}
    {location : Location} {updated : Heap}
    (allocation : AllocatesGeneralized heap function location updated)
    {oldLocation : Location} {cell : Cell}
    (read : Reads heap oldLocation cell) :
    Reads updated oldLocation cell := by
  cases allocation
  cases read with
  | intro selected => exact .intro selected.append_left

end AllocatesGeneralized

namespace Writes

theorem length_eq
    {heap updated : Heap} {location : Location} {value : Option Value}
    (write : Writes heap location value updated) :
    updated.cells.length = heap.cells.length := by
  cases write with
  | intro _ cellsWrite => exact cellsWrite.length_eq

theorem reads_updated
    {heap updated : Heap} {location : Location} {value : Option Value}
    (write : Writes heap location value updated) :
    ∃ previous,
      Reads heap location previous ∧
      Reads updated location { previous with value := value } := by
  cases write with
  | intro read cellsWrite =>
      exact ⟨_, read, .intro cellsWrite.reads_replacement⟩

theorem preserves_other
    {heap updated : Heap} {location other : Location}
    {value : Option Value} {cell : Cell}
    (write : Writes heap location value updated)
    (different : other ≠ location)
    (read : Reads heap other cell) :
    Reads updated other cell := by
  cases write with
  | intro _ cellsWrite =>
      cases read with
      | intro selected =>
          apply Reads.intro
          apply cellsWrite.preserves_other
          · intro equal
            apply different
            cases other
            cases location
            simp_all
          · exact selected

end Writes

end Heap

/-- A later heap preserves the static metadata of every old cell.  Ordinary
values may change, while declared types and principal generalized closures
remain fixed. -/
def HeapMetadataExtend (before after : Heap) : Prop :=
  ∀ location cell, Heap.Reads before location cell →
    ∃ updatedCell,
      Heap.Reads after location updatedCell ∧
      updatedCell.type = cell.type ∧
      updatedCell.generalized = cell.generalized

namespace HeapMetadataExtend

theorem refl (heap : Heap) : HeapMetadataExtend heap heap := by
  intro location cell read
  exact ⟨cell, read, rfl, rfl⟩

theorem trans {first middle last : Heap}
    (left : HeapMetadataExtend first middle)
    (right : HeapMetadataExtend middle last) :
    HeapMetadataExtend first last := by
  intro location cell read
  rcases left location cell read with
    ⟨middleCell, middleRead, middleType, middleGeneralized⟩
  rcases right location middleCell middleRead with
    ⟨lastCell, lastRead, lastType, lastGeneralized⟩
  exact ⟨lastCell, lastRead, lastType.trans middleType,
    lastGeneralized.trans middleGeneralized⟩

theorem of_allocation
    {before after : Heap} {type : Ty} {value : Option Value}
    {location : Location}
    (allocation : Heap.Allocates before type value location after) :
    HeapMetadataExtend before after := by
  intro oldLocation cell read
  exact ⟨cell, allocation.preserves_read read, rfl, rfl⟩

theorem of_generalized_allocation
    {before after : Heap} {function : GeneralizedClosure}
    {location : Location}
    (allocation : Heap.AllocatesGeneralized before function location after) :
    HeapMetadataExtend before after := by
  intro oldLocation cell read
  exact ⟨cell, allocation.preserves_read read, rfl, rfl⟩

theorem of_write
    {before after : Heap} {writtenLocation : Location}
    {value : Option Value}
    (write : Heap.Writes before writtenLocation value after) :
    HeapMetadataExtend before after := by
  intro location cell read
  by_cases same : location = writtenLocation
  · subst location
    rcases write.reads_updated with ⟨previous, previousRead, updatedRead⟩
    have cell_eq : cell = previous := read.functional previousRead
    subst cell
    exact ⟨{ previous with value := value }, updatedRead, rfl, rfl⟩
  · exact ⟨cell, write.preserves_other same read, rfl, rfl⟩

end HeapMetadataExtend

/-- Allocation followed by first-match lexical extension. -/
inductive Binds (environment : Environment) (heap : Heap)
    (id : Resolved.LocalId) (type : Ty) (value : Option Value) :
    Environment → Heap → Prop where
  | intro {location : Location} {updated : Heap}
      (allocation : Heap.Allocates heap type value location updated) :
      Binds environment heap id type value
        ((id, location) :: environment) updated

namespace Binds

theorem looksUp_self
    {environment before : Environment} {heap updated : Heap}
    {id : Resolved.LocalId} {type : Ty} {value : Option Value}
    (bind : Binds before heap id type value environment updated) :
    ∃ location,
      Environment.LooksUp environment id location := by
  cases bind
  exact ⟨_, .head⟩

theorem reads_bound
    {environment before : Environment} {heap updated : Heap}
    {id : Resolved.LocalId} {type : Ty} {value : Option Value}
    (bind : Binds before heap id type value environment updated) :
    ∃ location,
      Environment.LooksUp environment id location ∧
      Heap.Reads updated location { type := type, value := value } := by
  cases bind with
  | intro allocation =>
      exact ⟨_, .head, allocation.reads_new⟩

theorem preserves_read
    {environment before : Environment} {heap updated : Heap}
    {id : Resolved.LocalId} {type : Ty} {value : Option Value}
    (bind : Binds before heap id type value environment updated)
    {location : Location} {cell : Cell}
    (read : Heap.Reads heap location cell) :
    Heap.Reads updated location cell := by
  cases bind with
  | intro allocation => exact allocation.preserves_read read

end Binds

/-- Allocate a source-ordered vector of initialized binder values.  Each new
binding shadows the environment produced so far, exactly as sequential
parameter and pattern binding does at runtime. -/
inductive BindingsBind : Environment → Heap →
    List (Frontend.SourceInference.TypedBinder × Value) →
      Environment → Heap → Prop where
  | nil {environment heap} :
      BindingsBind environment heap [] environment heap
  | cons
      {environment middleEnvironment finalEnvironment : Environment}
      {before middleHeap finalHeap : Heap}
      {binder : Frontend.SourceInference.TypedBinder} {value : Value}
      {bindings : List (Frontend.SourceInference.TypedBinder × Value)}
      (head : Binds environment before binder.id binder.scheme.body
        (some value) middleEnvironment middleHeap)
      (tail : BindingsBind middleEnvironment middleHeap bindings
        finalEnvironment finalHeap) :
      BindingsBind environment before ((binder, value) :: bindings)
        finalEnvironment finalHeap

namespace BindingsBind

/-- The number of fresh cells is exactly the number of bindings. -/
theorem heap_length
    {environment finalEnvironment : Environment}
    {before after : Heap}
    {bindings : List (Frontend.SourceInference.TypedBinder × Value)}
    (bound : BindingsBind environment before bindings finalEnvironment after) :
    after.cells.length = before.cells.length + bindings.length := by
  induction bound with
  | nil => simp
  | cons head _ induction =>
      cases head with
      | intro allocation =>
          rw [induction, allocation.length_eq_succ]
          simp only [List.length_cons]
          omega

end BindingsBind

end Solcore.SourceSemantics.Dynamic
