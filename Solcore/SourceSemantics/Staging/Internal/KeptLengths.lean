import Solcore.SourceSemantics.Staging.RecursiveProfile
import Solcore.SourceSemantics.Dynamic.Preservation

/-!
# Kept array lengths

No staged step changes an array object's length. Allocations take fresh locations, an element write or a
memref store replaces one element, and a projected write cannot apply to an object. A bare write reaches only
a writable local, whose well-formed type is never an object's.
-/

set_option autoImplicit false

namespace Solcore.SourceSemantics.Staging.Recursive
open Frontend SourceInference TypeSystem Solcore.SourceSemantics.Dynamic

/-- Every array object of the earlier heap is still one at its location, with its element type and its
length. -/
def KeepsLengths (before after : Heap) : Prop :=
  ∀ location cell element elements, Heap.Reads before location cell →
    cell.value = some (.arrayObject element elements) →
    ∃ kept : Cell, ∃ updated : List Dynamic.Value, Heap.Reads after location kept ∧
      kept.value = some (.arrayObject element updated) ∧ updated.length = elements.length

namespace KeepsLengths

theorem refl (heap : Heap) : KeepsLengths heap heap :=
  fun _ cell _ elements read value => ⟨cell, elements, read, value, rfl⟩

theorem trans {first middle last : Heap} (left : KeepsLengths first middle) (right : KeepsLengths middle last) :
    KeepsLengths first last := by
  intro location cell element elements read value
  obtain ⟨kept, updated, keptRead, keptValue, keptLength⟩ := left location cell element elements read value
  obtain ⟨final, finalElements, finalRead, finalValue, finalLength⟩ :=
    right location kept element updated keptRead keptValue
  exact ⟨final, finalElements, finalRead, finalValue, finalLength.trans keptLength⟩

/-- A step that keeps every old cell keeps the lengths. -/
theorem of_reads {before after : Heap}
    (preserves : ∀ {location cell}, Heap.Reads before location cell → Heap.Reads after location cell) :
    KeepsLengths before after :=
  fun _ cell _ elements read value => ⟨cell, elements, preserves read, value, rfl⟩

theorem of_allocation {before after : Heap} {type : Ty} {value : Option Dynamic.Value} {location : Location}
    (allocation : Heap.Allocates before type value location after) : KeepsLengths before after :=
  of_reads allocation.preserves_read

theorem of_generalized_allocation {before after : Heap} {function : GeneralizedClosure} {location : Location}
    (allocation : Heap.AllocatesGeneralized before function location after) : KeepsLengths before after :=
  of_reads allocation.preserves_read

theorem of_copies {source : TypedSource} {environment copies : Dynamic.Environment} {before after : Heap}
    (copy : EnvironmentCopies source environment before copies after) : KeepsLengths before after :=
  of_reads copy.preserves_read

theorem of_binders {environment final : Dynamic.Environment} {before after : Heap}
    {binders : List TypedBinder} {values : List Dynamic.Value}
    (allocate : BindersAllocate environment before binders values final after) : KeepsLengths before after := by
  induction allocate with
  | nil => exact refl _
  | cons allocation _ ih => exact (of_allocation allocation).trans ih

theorem of_default {before after : Heap} {element : Ty} {zero : Dynamic.Value}
    (default : NewArrayDefault before element zero after) : KeepsLengths before after := by
  cases default with
  | word | fixed => exact refl _
  | array allocates => exact of_allocation allocates

/-- A write that leaves every array object an array object of its length keeps the lengths. -/
theorem of_write {before after : Heap} {location : Location} {value : Option Dynamic.Value}
    (write : Heap.Writes before location value after)
    (kept : ∀ cell element elements, Heap.Reads before location cell →
      cell.value = some (.arrayObject element elements) →
      ∃ updated, value = some (.arrayObject element updated) ∧ updated.length = elements.length) :
    KeepsLengths before after := by
  intro other cell element elements read stored
  by_cases same : other = location
  · subst same
    obtain ⟨updated, valueEq, length⟩ := kept cell element elements read stored
    obtain ⟨previous, previousRead, afterRead⟩ := write.reads_updated
    cases previousRead.functional read
    exact ⟨_, updated, afterRead, valueEq, length⟩
  · exact ⟨cell, elements, write.preserves_other same read, stored, rfl⟩

/-- A place write keeps the lengths when it reaches an object only through a projection: the projection is
then an element's, which replaces one element. -/
theorem of_place_write {Modify : Option Dynamic.Value → Dynamic.Value → Prop} {before after : Heap}
    {target : ResolvedPlace} {updated : Dynamic.Value}
    (write : ResolvedPlaceWrites Modify before target updated after)
    (projected : ∀ cell element elements, Heap.Reads before target.location cell →
      cell.value = some (.arrayObject element elements) → target.projections ≠ []) :
    KeepsLengths before after := by
  cases write with
  | intro currentRead _rootType initialValue update heapWrite =>
      rename_i currentCell initial
      apply of_write heapWrite
      intro cell element elements read stored
      cases read.functional currentRead
      have nonempty := projected _ element elements currentRead stored
      have initialEq : initial = some (.arrayObject element elements) := by
        cases initialValue <;> simp_all
      subst initialEq
      generalize target.projections = projections at update nonempty
      cases update with
      | leaf => exact (nonempty rfl).elim
      | element _ _ replace => exact ⟨_, rfl, replace.length_eq⟩

/-- An array form after its children allocates or replaces one element of an object. -/
theorem of_array_outcome {form : ExpressionForm} {values : List Dynamic.Value} {before after : Heap}
    {outcome : Outcome} (result : ArrayOutcome form values before outcome after) : KeepsLengths before after := by
  cases result with
  | newArray _ default allocates => exact (of_default default).trans (of_allocation allocates)
  | arrayLiteral allocates => exact of_allocation allocates
  | toArray _ allocates => exact of_allocation allocates
  | memrefStore read current replace write =>
      apply of_write write
      intro cell element elements cellRead stored
      cases cellRead.functional read
      rw [current] at stored
      cases stored
      exact ⟨_, rfl, replace.length_eq⟩
  | _ => exact refl _

end KeepsLengths

private def applicationHead : Ty → Ty
  | .application function _ => applicationHead function
  | type => type

private theorem applicationHead_applyMany (start : Ty) (arguments : List Ty) :
    applicationHead (Ty.applyMany start arguments) = applicationHead start := by
  induction arguments generalizing start with
  | nil => rfl
  | cons argument rest ih =>
      show applicationHead (Ty.applyMany (.application start argument) rest) = applicationHead start
      rw [ih]
      rfl

/-- No case of `TypeWellScoped` builds an array object's type: there is no general application case, a
nominal type has a declaration at its head, and the other applied builtins are other types. -/
theorem arrayObject_not_wellScoped {context : Context} {flexible : List TypeSystem.TypeVarId} {element : Ty} :
    ¬ TypeWellScoped context flexible (Ty.arrayObject element) := by
  intro wellScoped
  generalize equal : Ty.arrayObject element = type at wellScoped
  cases wellScoped with
  | nominal dataType arguments =>
      have heads := congrArg applicationHead equal
      simp only [Ty.nominal, applicationHead_applyMany, Ty.arrayObject, applicationHead] at heads
      cases heads
  | contractNominal contract arguments =>
      have heads := congrArg applicationHead equal
      simp only [Ty.nominal, applicationHead_applyMany, Ty.arrayObject, applicationHead] at heads
      cases heads
  | _ => simp [Ty.arrayObject, Ty.array, Ty.arraySlice, Ty.memref] at equal

private theorem comptime_inner_wellScoped {context : Context} {flexible : List TypeSystem.TypeVarId}
    {inner : Ty} (wellScoped : TypeWellScoped context flexible (.comptime inner)) :
    TypeWellScoped context flexible inner := by
  generalize equal : Ty.comptime inner = type at wellScoped
  cases wellScoped with
  | comptime innerScoped => cases equal; exact innerScoped
  | nominal dataType arguments =>
      have heads := congrArg applicationHead equal
      simp only [Ty.nominal, applicationHead_applyMany, applicationHead] at heads
      cases heads
  | contractNominal contract arguments =>
      have heads := congrArg applicationHead equal
      simp only [Ty.nominal, applicationHead_applyMany, applicationHead] at heads
      cases heads
  | _ => simp [Ty.array, Ty.arraySlice, Ty.memref] at equal

/-- A value that is an array object has no well-scoped type. -/
theorem arrayObject_type_not_wellScoped {context other : Context} {heap : Heap} {flexible : List TypeSystem.TypeVarId}
    {element : Ty} {elements : List Dynamic.Value} :
    ∀ {type : Ty}, ValueHasType context heap (.arrayObject element elements) type →
      ¬ TypeWellScoped other flexible type
  | _, .arrayObject _ => arrayObject_not_wellScoped
  | _, .comptime inner => fun wellScoped =>
      arrayObject_type_not_wellScoped inner (comptime_inner_wellScoped wellScoped)

/-- A writable local's cell holds no array object: the local's type is well formed, and the cell has it. -/
theorem writable_not_object {context : Context} {environment : Dynamic.Environment} {heap : Heap}
    {root : Resolved.LocalId} {location : Location} {type : Ty}
    (locals : EnvironmentAgrees heap context.locals environment) (heapTyped : HeapWellTyped context heap)
    (writable : WritableLocal context root type) (lookup : Environment.LooksUp environment root location) :
    ∀ cell element elements, Heap.Reads heap location cell → cell.value ≠ some (.arrayObject element elements) := by
  intro cell element elements read stored
  obtain ⟨scheme, staticLookup, wellFormed, _, _⟩ := writable.scheme
  obtain ⟨found, foundCell, foundLookup, foundRead, cellType, _⟩ := locals.lookup staticLookup
  cases lookup.functional foundLookup
  cases read.functional foundRead
  have typed := (heapTyped _ foundRead.member).value
  rw [stored] at typed
  cases typed with
  | some valueTyped =>
      rw [cellType] at valueTyped
      exact arrayObject_type_not_wellScoped valueTyped wellFormed.body

end Solcore.SourceSemantics.Staging.Recursive
