import Solcore.SourceSemantics.CoreLowering.DataPlaceCommitReflection

/-! The actual final storeCell updates a mapped source cell between administrative
cells. Two runtime aliases observe that same update, while source metadata and
both administrative sentinels remain unchanged. -/
set_option autoImplicit false
namespace Tests.SourceCoreDataPlaceCommitReflection
open Solcore Solcore.Core Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering
open GeneralHeap DataPayload

private def catalog : SourceCoreDataCatalog.Catalog := {}
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private def functions : GenericHeap.PayloadModel catalog where
  Represents := fun _ _ _ _ _ _ => False
  projection := False.elim
  runtime_hasType := False.elim
  extend := fun impossible _ _ => False.elim impossible
private def model := payloadModel catalog signatures functions
private def cell : Dynamic.Cell := ⟨.bool, some (.bool false), none⟩
private def heap : Dynamic.Heap := ⟨[cell]⟩
private def finalHeap : Dynamic.Heap := ⟨[{cell with value := some (.bool true)}]⟩
private def world : StoreTyping := [.integer, OptionalCell.cellType .bool, .integer]
private def store : Store := [.integer 900, .inRight .unit (.bool false), .integer 901]
private def finalStore : Store := [.integer 900, .inRight .unit (.bool true), .integer 901]
private def reference : Value := .cellRef (OptionalCell.cellType .bool) 1
private def environment : Environment := [reference, .bool true, reference]
private def expression : Expr := .storeCell (.var 0) (.inRight .unit (.var 1))
private theorem heapRelated : GenericHeap.HeapRepresents model [1] world heap store := by
  have empty : GenericHeap.HeapRepresents model [] [] ⟨[]⟩ [] := .empty
  have withPrefix := empty.allocate_administrative (value := .integer 900) .integer
  exact (withPrefix.allocate (.initialized (.bool false)) .append).1.allocate_administrative .integer
private theorem ran : runStateful 30 (.initial expression environment store) = .done .unit finalStore := by cbv

example : ∃ after,
    Dynamic.Heap.Writes heap ⟨0⟩ (some (.bool true)) after ∧
    GenericHeap.HeapRepresents model [1] world after finalStore ∧
    AdministrativePreserved [1] store [1] finalStore ∧
    Dynamic.HeapMetadataExtend heap after ∧
    finalStore.read? 1 = some (.inRight .unit (.bool true)) := by
  obtain ⟨after, _, written, heaps, frame, metadata, observed⟩ :=
    DataPlaceCommitReflection.reflects_storeCell heapRelated
      (show ReferenceRepresents [1] world ⟨0⟩ 1 .bool from ⟨rfl, rfl⟩)
      (.intro .head) (show model.Represents [1] world .bool (.bool true) (.bool true) .bool from .bool true)
      (.var rfl) (.var rfl) (runStateful_evaluation_sound ran)
  exact ⟨after, written, heaps, frame, metadata, observed⟩

/-- Allocation metadata remains exactly the source declaration's metadata. -/
example : Dynamic.Heap.Writes heap ⟨0⟩ (some (.bool true)) finalHeap :=
  DataPlaceCommitReflection.source_writes (.intro .head) _

/-- Both aliases see the update; they are not copies of the previous payload. -/
example : runStateful 50 (.initial
    (.letE expression (.pair (.loadCell (.var 1)) (.loadCell (.var 3)))) environment store) =
      .done (.pair (.inRight .unit (.bool true)) (.inRight .unit (.bool true))) finalStore := by cbv

/-- Reinterpreting a reconstructed root with an authenticated modifier keeps
the first duplicate's position and the remaining entries unchanged. -/
example : Dynamic.ProjectionsUpdate
    (fun _ value => Dynamic.AssignmentValueApplies .equal (some (.bool false)) (.bool true) value)
    (some (.mapping .bool .bool [(.bool true, .bool false), (.bool true, .bool false)]))
    [.index (.bool true)]
    (.mapping .bool .bool [(.bool true, .bool true), (.bool true, .bool false)]) := by
  apply DataPlaceCommitReflection.update_of_replacement
    (replacement := .bool true)
  · exact .indexFound (.head ⟨rfl, .bool true⟩) (.leaf rfl) (.update (.head ⟨rfl, .bool true⟩))
  · intro snapshot
    exact .equal _ _

end Tests.SourceCoreDataPlaceCommitReflection
