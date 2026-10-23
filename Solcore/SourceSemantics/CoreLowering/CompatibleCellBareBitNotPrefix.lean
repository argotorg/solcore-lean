import Solcore.SourceSemantics.CoreLowering.CompatibleRenamedBareBitNotNative
import Solcore.SourceSemantics.CoreLowering.CompatibleBareBitNotMeaning
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedBareAssignmentContracts
import Solcore.SourceSemantics.CoreLowering.CompatibleCellBareAssignmentCommit

/-! A numeric bare snapshot creates a real mapped commit and an exact typed
seven-slot continuation in the actual renamed environment. Its Unit RHS has
no source child. Every native phase is constructed from a represented live cell. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleRenamedBareBitNot
open Core Frontend SourceInference GeneralHeap CoreProof DataPatternValues
open CompatiblePayload CompatibleEquality CompatibleHeap DataEquality
open SourceCoreCompatibleDataPlaces DataPlaceExecution CompatibleBareBitNotCertificates

variable {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
  {ambient : AmbientDefinitions checked.catalog.definitions} {functions : FunctionModel checked.catalog ambient}
  {prepared : Prepared} {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
  {location : Dynamic.Location} {target : Location} {sourceValue : Dynamic.Value} {value : Value}
  {cells : GenericHeap.CellModel ambient.definitions}
  {instances : GeneralizedLocalDescriptorHeap.InstanceModel ambient.definitions}
  {actual : Environment} {actualContext : Core.Context} {index : Nat} {ξ : Renaming}

/-! The actual six phases and write expose a strict child of the original
Core derivation. Source updates have no expression child; continuation
agreement transports results but supplies no execution-size bound. -/
theorem initialized_prefix_cells_sized (layout : Layout prepared)

    (profile : SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = .word ∨
      SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = .integer)
    (ordinaryCells : GenericHeap.OrdinaryCells (payloadModel checked registry functions) cells)
    (heaps : GenericHeap.CellHeapRepresents cells mapping world heap store)
    (reference : ReferenceRepresents mapping world location target prepared.route.rootType)
    (read : Dynamic.Heap.Reads heap location ⟨prepared.route.rootSourceType, some sourceValue, none⟩)
    (nativeRead : store.read? target = some (.inRight .unit value))
    (represented : ValueRep checked registry functions mapping world prepared.route.rootSourceType sourceValue value prepared.route.rootType)
    (lookup : actual[ξ index]? = some (.cellRef (OptionalCell.cellType prepared.route.rootType) target))
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (operator : Option BinaryOp) (invalid : Word) :
    ∃ updated replacement after finalStore slots,
      Dynamic.BitNotSnapshot (some sourceValue) updated ∧
      Dynamic.Heap.Writes heap location (some updated) after ∧
      ValueRep checked registry functions mapping world prepared.route.rootSourceType updated replacement prepared.route.rootType ∧
      GenericHeap.CellHeapRepresents cells mapping world after finalStore ∧
      AdministrativePreserved mapping store mapping finalStore ∧ Dynamic.HeapMetadataExtend heap after ∧
      CellAwareScopeAuthority.Effect instances mapping world heap store mapping world after finalStore ∧
      slots.length = 7 ∧ RuntimeEnvironmentHasTypes world (slots ++ actual) (writtenContext prepared actualContext) ambient.definitions ∧
      (∀ next output, ContinuationAgreement actual store
        ((execute prepared (.var index) (SourceCoreCalls.packArguments []) (LanguageResult.success .unit)
          next output operator true invalid).rename ξ)
        (slots ++ actual) finalStore (shift 7 (next.rename ξ))) ∧
      ∀ {next : Expr} {output : Ty} {result : Value} {after : Store} {size : Nat},
        CoreProof.EvaluationSize size actual store
          ((execute prepared (.var index) (SourceCoreCalls.packArguments []) (LanguageResult.success .unit)
            next output operator true invalid).rename ξ) result after →
        ∃ remainingSize, remainingSize < size ∧ CoreProof.EvaluationSize remainingSize (slots ++ actual)
          finalStore (shift 7 (next.rename ξ)) result after := by
  obtain ⟨updated, replacement, related, applies, modified, _⟩ :=
    CompatiblePlaceNumericBitNotModifier.success profile represented
      (environment := rhsEnvironment prepared.route.rootType target .unit (.inRight .unit value) .unit actual)
      (snapshot := .var 1) (rhs := .var 0) (.var rfl) operator store invalid
  have written := DataPlaceCommitReflection.source_writes read updated
  obtain ⟨finalStore, coreWritten, finalHeaps, frame⟩ := heaps.write_initialized ordinaryCells reference read rfl related written
  have writeEffect : CellAwareScopeAuthority.Effect instances mapping world heap store mapping world
      ⟨heap.cells.set location.index ⟨prepared.route.rootSourceType, some updated, none⟩⟩ finalStore :=
    .write_ordinary heaps.injective read rfl reference written coreWritten
  let slots : Environment := [.unit, replacement, replacement, .unit, .inRight .unit value, .unit,
    .cellRef (OptionalCell.cellType prepared.route.rootType) target]
  have rhs : Evaluates (snapshotEnvironment prepared.route.rootType target .unit (.inRight .unit value) actual)
      store (shift 3 (LanguageResult.success .unit)) (.inRight .word .unit) store := by
    simp only [shift, List.range, List.range.loop, List.foldl, Expr.weakenAt, LanguageResult.success]
    exact .inRight .unit
  have modifier : Evaluates (rhsEnvironment prepared.route.rootType target .unit (.inRight .unit value) .unit actual)
      store (SourceCoreCompatibleDataPlaces.modified prepared.route.leafType operator true (.var 1) (.var 0) invalid)
      (.inRight .word replacement) store := by simpa only [← layout.sameType] using modified
  have agreement : ∀ next output, ContinuationAgreement actual store
      ((execute prepared (.var index) (SourceCoreCalls.packArguments []) (LanguageResult.success .unit)
        next output operator true invalid).rename ξ)
      (slots ++ actual) finalStore (shift 7 (next.rename ξ)) := by
    intro next output
    rw [execute_rename layout]
    exact (ContinuationAgreement.letE (.var lookup)).trans
      ((ContinuationAgreement.bind (CompatibleBareBitNotNative.keys_evaluates _ _)).trans
        ((ContinuationAgreement.bind (CompatibleBareBitNotNative.getter_evaluates layout nativeRead)).trans
          ((ContinuationAgreement.bind rhs).trans
            ((ContinuationAgreement.bind modifier).trans
              ((ContinuationAgreement.bind (CompatibleBareBitNotNative.setter_evaluates layout
                (.inRight .unit value) replacement nativeRead)).trans
                (ContinuationAgreement.letE (.storeCell (.var rfl) nativeRead (.inRight (.var rfl)) coreWritten)))))))

  refine ⟨updated, replacement, _, finalStore, slots, applies, written, related, finalHeaps, frame,
    .of_write written, writeEffect, rfl, ?_, agreement, ?_⟩
  ·
    exact .cons .unit (.cons related.runtime_hasType (.cons related.runtime_hasType
      (.cons .unit (.cons (.inRight represented.runtime_hasType) (.cons .unit (.cons (.cellRef reference.typed) actualTyped))))))
  · intro next output result after size completed
    have terminal := (agreement .unit output).wrap
      (by simpa [shift, Expr.rename, List.range, List.range.loop, List.foldl, Expr.weakenAt] using
        (Evaluates.unit (environment := slots ++ actual) (store := finalStore)))
    rw [execute_rename layout] at terminal completed
    exact RecursiveNamedBareAssignmentContracts.execute_continuation_sized
      (.var lookup) (CompatibleBareBitNotNative.keys_evaluates _ _)
      (CompatibleBareBitNotNative.getter_evaluates layout nativeRead) rhs modifier
      (CompatibleBareBitNotNative.setter_evaluates layout (.inRight .unit value) replacement nativeRead)
      terminal completed

end Solcore.SourceSemantics.CoreLowering.CompatibleRenamedBareBitNot
