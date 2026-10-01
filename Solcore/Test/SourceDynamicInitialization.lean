import Solcore.SourceSemantics.Dynamic.Initialization

/-! Successful expression execution preserves initialization of existing
locations, without typing assumptions. The stronger property excludes clearing
writes even though the independent heap relation can describe them. -/
set_option autoImplicit false
namespace Tests.SourceDynamicInitialization
open Solcore Solcore.SourceSemantics Solcore.SourceSemantics.Dynamic
open Solcore.Frontend Solcore.Frontend.SourceInference

example {program : Program} {context : SourceSemantics.Context} {evidence : EvidenceEnvironment}
    {source : TypedSource} {environment : Environment} {before after : Heap}
    {id : ExpressionId} {value : Value} {location : Location} {cell : Cell}
    (trace : ExpressionEvaluates program context evidence source environment before id value after)
    (read : Heap.Reads before location cell) (initialized : cell.value ≠ none) :
    ∃ current, Heap.Reads after location current ∧ current.value ≠ none :=
  trace.initialization_extends location cell read initialized

private def initialized : Cell := ⟨.bool, some (.bool false), none⟩
private def cleared : Cell := ⟨.bool, none, none⟩

example : Heap.Writes ⟨[initialized]⟩ ⟨0⟩ none ⟨[cleared]⟩ :=
  .intro (.intro .head) .head

example : ¬ HeapInitializationExtend ⟨[initialized]⟩ ⟨[cleared]⟩ := by
  intro extension
  obtain ⟨current, read, nonempty⟩ := extension ⟨0⟩ initialized (.intro .head) (by decide)
  have same := read.functional (show Heap.Reads ⟨[cleared]⟩ ⟨0⟩ cleared from .intro .head)
  subst current
  exact nonempty rfl

example {before middle after : Heap} {location : Location} {cell : Cell}
    {type : TypeSystem.Ty} {allocated : Location} {value : Value}
    (read : Heap.Reads before location cell) (initialized : cell.value ≠ none)
    (allocation : Heap.Allocates before type none allocated middle)
    (write : Heap.Writes middle allocated (some value) after) :
    ∃ current, Heap.Reads after location current ∧ current.value ≠ none :=
  ((HeapInitializationExtend.of_allocation allocation).trans
    (HeapInitializationExtend.of_write write)) location cell read initialized

#print axioms ExpressionEvaluates.initialization_extends
#print axioms StatementExecutes.initialization_extends
#print axioms ForLoopExecutes.initialization_extends
end Tests.SourceDynamicInitialization
