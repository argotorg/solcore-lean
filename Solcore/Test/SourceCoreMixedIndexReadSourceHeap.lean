import Solcore.Test.SourceCoreMixedIndexReadSource

/-! The mapping root is updated in the heap reached by the right-hand call.
All earlier cells and the exact appended parameter cells remain present. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreMixedIndexRead
open Solcore Core Frontend SourceInference SourceSemantics
open Tests.SourceCoreMixedImperative

def mappingValue (value : Word) : Dynamic.Value :=
  .mapping .word .word [(.word (Word.ofNatModulo 3),.word value)]
def phaseHeap (base : Dynamic.Heap) (value : Option Word) (active : Bool)
    (suffix : List Dynamic.Cell) : Dynamic.Heap :=
  ⟨base.cells ++ [⟨mappingType,value.map mappingValue,none⟩,⟨.bool,some (.bool active),none⟩] ++ suffix⟩
def phaseEnvironment {source : TypedSource} (shape : Shape source)
    (base : Dynamic.Heap) (environment : Dynamic.Environment) : Dynamic.Environment :=
  (shape.active.id,⟨base.cells.length+1⟩) :: (shape.table.id,⟨base.cells.length⟩) :: environment

theorem phaseHeap.prefix (base : Dynamic.Heap) (value : Option Word) (active : Bool)
    (suffix : List Dynamic.Cell) : HeapAppends base (phaseHeap base value active suffix) :=
  ⟨_,List.append_assoc _ _ _⟩

private theorem cell_append (earlier : List Dynamic.Cell) {tail : List Dynamic.Cell}
    {index : Nat} {cell : Dynamic.Cell} (read : Dynamic.Heap.CellAt tail index cell) :
    Dynamic.Heap.CellAt (earlier ++ tail) (earlier.length + index) cell := by
  induction earlier with
  | nil => simpa using read
  | cons head rest ih => simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using Dynamic.Heap.CellAt.tail ih

private theorem write_append (earlier : List Dynamic.Cell) {before after : List Dynamic.Cell}
    {index : Nat} {cell : Dynamic.Cell} (write : Dynamic.Heap.CellsWrite before index cell after) :
    Dynamic.Heap.CellsWrite (earlier ++ before) (earlier.length + index) cell (earlier ++ after) := by
  induction earlier with
  | nil => simpa using write
  | cons head rest ih => simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using Dynamic.Heap.CellsWrite.tail ih

theorem phaseHeap.table (base : Dynamic.Heap) (value : Option Word) (active : Bool) (suffix : List Dynamic.Cell) :
    Dynamic.Heap.Reads (phaseHeap base value active suffix) ⟨base.cells.length⟩
      ⟨mappingType,value.map mappingValue,none⟩ := by
  apply Dynamic.Heap.Reads.intro
  simpa only [phaseHeap,List.append_assoc,List.cons_append,List.nil_append,Nat.add_zero] using
    cell_append base.cells (Dynamic.Heap.CellAt.head (cells := ⟨.bool,some (.bool active),none⟩ :: suffix))

theorem phaseHeap.active (base : Dynamic.Heap) (value : Option Word) (active : Bool) (suffix : List Dynamic.Cell) :
    Dynamic.Heap.Reads (phaseHeap base value active suffix) ⟨base.cells.length+1⟩ ⟨.bool,some (.bool active),none⟩ := by
  apply Dynamic.Heap.Reads.intro
  simpa only [phaseHeap,List.append_assoc,List.cons_append,List.nil_append] using
    cell_append base.cells (Dynamic.Heap.CellAt.tail (cell := ⟨mappingType,value.map mappingValue,none⟩)
      (Dynamic.Heap.CellAt.head (cells := suffix)))

theorem phaseHeap.write_table (base : Dynamic.Heap) (value : Option Word) (next : Word)
    (active : Bool) (suffix : List Dynamic.Cell) :
    Dynamic.Heap.Writes (phaseHeap base value active suffix) ⟨base.cells.length⟩
      (some (mappingValue next)) (phaseHeap base (some next) active suffix) := by
  apply Dynamic.Heap.Writes.intro (phaseHeap.table base value active suffix)
  simpa only [phaseHeap,List.append_assoc,List.cons_append,List.nil_append,Nat.add_zero,Option.map_some] using
    write_append base.cells (Dynamic.Heap.CellsWrite.head
      (previous := ⟨mappingType,value.map mappingValue,none⟩)
      (replacement := ⟨mappingType,some (mappingValue next),none⟩)
      (rest := ⟨.bool,some (.bool active),none⟩ :: suffix))

theorem phaseHeap.write_active (base : Dynamic.Heap) (value : Option Word)
    (active next : Bool) (suffix : List Dynamic.Cell) :
    Dynamic.Heap.Writes (phaseHeap base value active suffix) ⟨base.cells.length+1⟩
      (some (.bool next)) (phaseHeap base value next suffix) := by
  apply Dynamic.Heap.Writes.intro (phaseHeap.active base value active suffix)
  simpa only [phaseHeap,List.append_assoc,List.cons_append,List.nil_append] using
    write_append base.cells (Dynamic.Heap.CellsWrite.tail (previous := ⟨mappingType,value.map mappingValue,none⟩)
      (Dynamic.Heap.CellsWrite.head (previous := ⟨.bool,some (.bool active),none⟩)
        (replacement := ⟨.bool,some (.bool next),none⟩) (rest := suffix)))

theorem Shape.active_stored {source : TypedSource} (shape : Shape source) (base : Dynamic.Heap)
    (environment : Dynamic.Environment) (value : Option Word) (active : Bool) (suffix : List Dynamic.Cell) :
    StoredValue shape.active (phaseEnvironment shape base environment) (phaseHeap base value active suffix) (.bool active) :=
  ⟨_,_,.head,phaseHeap.active base value active suffix,rfl,rfl⟩
theorem Shape.table_stored {source : TypedSource} (shape : Shape source) (base : Dynamic.Heap)
    (environment : Dynamic.Environment) (value : Word) (active : Bool) (suffix : List Dynamic.Cell) :
    StoredValue shape.table (phaseEnvironment shape base environment) (phaseHeap base (some value) active suffix)
      (mappingValue value) :=
  ⟨_,_,.tail shape.activeTable .head,phaseHeap.table base (some value) active suffix,rfl,rfl⟩

theorem projected_first {program : SourceSemantics.Program} {source : TypedSource}
    {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {environment : Dynamic.Environment} {base : Dynamic.Heap} {active : Bool} {suffix : List Dynamic.Cell}
    {root : Resolved.LocalId} {key rhs : ExpressionId} {right : Word}
    (lookup : Dynamic.Environment.LooksUp environment root ⟨base.cells.length⟩)
    (keyTrace : Dynamic.ExpressionEvaluates program context evidence source environment
      (phaseHeap base none active []) key (.word (Word.ofNatModulo 3)) (phaseHeap base none active []))
    (rightTrace : Dynamic.ExpressionEvaluates program context evidence source environment
      (phaseHeap base none active []) rhs (.word right) (phaseHeap base none active suffix)) :
    Dynamic.SourcePlaceAssignment program context evidence source (Dynamic.AssignmentValueApplies .equal)
      environment (phaseHeap base none active []) ⟨root,[.index key],.word⟩ rhs (mappingValue right)
      (phaseHeap base (some right) active suffix) := by
  exact .intro (.intro lookup (phaseHeap.table base none active []) (.index keyTrace .nil)
    (phaseHeap.table base none active []) (.emptyMapping .word .word) (.indexDefault .nil .word .nil))
    rightTrace (.intro (phaseHeap.table base none active suffix) rfl (.emptyMapping .word .word)
      (.indexDefault .nil .word (.leaf (.equal _ _)) (.append .nil))
      (phaseHeap.write_table base none right active suffix))

theorem projected_add {program : SourceSemantics.Program} {source : TypedSource}
    {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {environment : Dynamic.Environment} {base : Dynamic.Heap} {active : Bool} {suffix : List Dynamic.Cell}
    {root : Resolved.LocalId} {key rhs : ExpressionId} {old right : Word}
    (lookup : Dynamic.Environment.LooksUp environment root ⟨base.cells.length⟩)
    (keyTrace : Dynamic.ExpressionEvaluates program context evidence source environment
      (phaseHeap base (some old) active suffix) key (.word (Word.ofNatModulo 3)) (phaseHeap base (some old) active suffix))
    (rightTrace : Dynamic.ExpressionEvaluates program context evidence source environment
      (phaseHeap base (some old) active suffix) rhs (.word right) (phaseHeap base (some old) active suffix)) :
    Dynamic.SourcePlaceAssignment program context evidence source (Dynamic.AssignmentValueApplies .add)
      environment (phaseHeap base (some old) active suffix) ⟨root,[.index key],.word⟩ rhs (mappingValue (old.add right))
      (phaseHeap base (some (old.add right)) active suffix) := by
  exact .intro (.intro lookup (phaseHeap.table base (some old) active suffix) (.index keyTrace .nil)
    (phaseHeap.table base (some old) active suffix) .initialized (.indexFound (.head (.refl (.word _))) .nil))
    rightTrace (.intro (phaseHeap.table base (some old) active suffix) rfl .initialized
      (.indexFound (.head (.refl (.word _))) (.leaf (.add (.wordAdd _ _))) (.update (.head (.refl (.word _)))))
      (phaseHeap.write_table base (some old) (old.add right) active suffix))

end Tests.SourceCoreMixedIndexRead
