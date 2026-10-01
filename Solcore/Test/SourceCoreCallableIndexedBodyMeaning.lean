import Solcore.SourceSemantics.CoreLowering.CallableIndexedNamedBodyMeaning

/-! A mapped source update survives a language failure inside the context
wrapper. Installation/restoration preserve the general payload model and the
original caller. No child Core execution is supplied to the regression. -/
set_option autoImplicit false
namespace Solcore.Test.SourceCoreCallableIndexedBodyMeaning
open Core Frontend SourceSemantics SourceSemantics.CoreLowering GeneralHeap
open CallableAncestryPairedLookup CallableIndexedHistory
open SourceCoreCallableIndexedFrames

example {checked : Checked} {base : Base checked} {inputs : Inputs base} {table : Table}
    {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
    {model : GenericHeap.PayloadModel catalog projects} {layout : Layout}
    {world : StoreTyping} {before after : Dynamic.Heap} {store : Store}
    {current next : NativeFrame} {currentGhost nextGhost : GhostFrame}
    {sourceLocation : Dynamic.Location} {cell : Dynamic.Cell} {reason : Word}
    (registered : layout.Registered catalog.definitions)
    (heaps : GenericHeap.HeapRepresents model [1] world before store)
    (contextTyped : world[0]? = some layout.type)
    (caller : CellState inputs table layout 0 current currentGhost store)
    (nextHistory : Current inputs table next nextGhost)
    (reference : ReferenceRepresents [1] world sourceLocation 1 .bool)
    (read : Dynamic.Heap.Reads before sourceLocation cell)
    (represented : model.Represents [1] world cell.type (.bool true) (.bool true) .bool)
    (written : Dynamic.Heap.Writes before sourceLocation (some (.bool true)) after) :
    ∃ finalStore,
      Evaluates [.cellRef (OptionalCell.cellType .bool) 1, .cellRef layout.type 0] store
        (withFrame (.var 1) (SourceCoreCallableIndexedDispatch.literal layout next)
          (.letE (.storeCell (.var 0) (.inRight .unit (.bool true)))
            (LanguageResult.failure .unit (.word reason))))
        (.inLeft .unit (.word reason)) finalStore ∧
      GenericHeap.HeapRepresents model [1] world after finalStore ∧
      AdministrativePreserved [1] store [1] finalStore ∧
      CellState inputs table layout 0 current currentGhost finalStore ∧
      finalStore.read? 1 = some (.inRight .unit (.bool true)) := by
  have unmapped : (0 : Nat) ∉ ([1] : LocationMap) := by decide
  obtain ⟨installedHeaps, installedCurrent⟩ := CallableIndexedBodyFrames.install
    registered heaps unmapped contextTyped caller nextHistory
  obtain ⟨updated, nativeWrite, updatedHeaps, sourceFrame⟩ :=
    installedHeaps.write_initialized reference read represented written
  obtain ⟨old, oldRead, _⟩ := installedHeaps.runtime_hasTypes.lookup reference.typed
  have bodyEvaluation : Evaluates
      [.unit, encode layout current, .cellRef (OptionalCell.cellType .bool) 1, .cellRef layout.type 0]
      (store.set 0 (encode layout next))
      (((Expr.letE (.storeCell (.var 0) (.inRight .unit (.bool true)))
        (LanguageResult.failure .unit (.word reason))).weakenAt 0).weakenAt 0)
      (.inLeft .unit (.word reason)) updated := by
    simpa [Expr.weakenAt, LanguageResult.failure] using
      (show Evaluates
        [.unit, encode layout current, .cellRef (OptionalCell.cellType .bool) 1, .cellRef layout.type 0]
        (store.set 0 (encode layout next))
        (.letE (.storeCell (.var 2) (.inRight .unit (.bool true))) (.inLeft .unit (.word reason)))
        (.inLeft .unit (.word reason)) updated from
        .letE (.storeCell (.var rfl) oldRead (.inRight .bool) nativeWrite) (.inLeft .word))
  have nextEvaluation : Evaluates
      [encode layout current, .cellRef (OptionalCell.cellType .bool) 1, .cellRef layout.type 0] store
      ((SourceCoreCallableIndexedDispatch.literal layout next).weakenAt 0) (encode layout next) store := by
    rw [← Expr.rename_insertion, CallableIndexedRenaming.literal]
    exact CallableIndexedContextFrames.literal_evaluates _ _ _ _
  have evaluated := CallableContextFrames.withFrame_evaluates (.var (show
      ([.cellRef (OptionalCell.cellType .bool) 1, .cellRef layout.type 0] : Environment)[1]? = some (.cellRef layout.type 0) from rfl))
    caller.read nextEvaluation bodyEvaluation
  have _innerCurrent := CallableIndexedBodyFrames.body_current unmapped installedCurrent sourceFrame
  obtain ⟨finalHeaps, finalFrame, finalCaller⟩ := CallableIndexedBodyFrames.restore
    registered unmapped contextTyped caller updatedHeaps (WorldExtends.refl _) sourceFrame
  refine ⟨_, evaluated, finalHeaps, finalFrame, finalCaller, ?_⟩
  have restoreWrite : updated.write? 0 (encode layout current) = some (updated.set 0 (encode layout current)) :=
    Store.write?_eq_some_iff.mpr ⟨updatedHeaps.runtime_hasTypes.location_lt contextTyped, rfl⟩
  exact (Store.write?_preserves_other restoreWrite (by decide)).trans (Store.write?_reads_written nativeWrite)

/-- Repeated nested body frames preserve the same installed history before
the enclosing wrapper restores its caller. -/
example {checked : Checked} {base : Base checked} {inputs : Inputs base} {table : Table}
    {layout : Layout} {firstMap middleMap finalMap : LocationMap} {first middle final : Store}
    {location : Location} {native : NativeFrame} {ghost : GhostFrame}
    (unmapped : location ∉ firstMap)
    (current : CellState inputs table layout location native ghost first)
    (firstFrame : AdministrativePreserved firstMap first middleMap middle)
    (secondFrame : AdministrativePreserved middleMap middle finalMap final) :
    CellState inputs table layout location native ghost final :=
  CallableIndexedBodyFrames.body_current unmapped current (firstFrame.trans secondFrame)

end Solcore.Test.SourceCoreCallableIndexedBodyMeaning
