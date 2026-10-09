import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualInitializedClosureReceipts

/-! Actual writes update positive contextual closure receipts at the same
Source/native cell. Writes to other cells preserve their live reads using
the genuine injective location map. Administrative transport supplies neither
of these facts. This module covers ordinary initialized closure cells. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualStoredClosureWriteReceipts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionValues (Header Key)
open CallableIndexedOwnedContextualStoredClosureAssociationReceipts (Member)
open CallableIndexedOwnedContextualInitializedClosureReceipts (StoredAt payload_member)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {mapping : LocationMap} {world : StoreTyping}
  {function : Dynamic.Closure} {native : Core.Value}
  {bindings : List CallableIndexedParameterCertificates.Binding} {parameter result : Ty}

/-- One original initialized write returns its full heap/frame receipts and
the new positive payload at the actual written cell. Its Source declaration
type is authenticated independently of the projected native function type. -/
theorem written_member
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    {heap after : Dynamic.Heap} {store : Store} {location : Dynamic.Location}
    {target : Core.Location} {cell : Dynamic.Cell}
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
      (CallableIndexedOwnedGeneralLambdaValues.model headers keys registry faults profile)
      mapping world heap store)
    (reference : ReferenceRepresents mapping world location target (CallableContract.functionType parameter result))
    (read : Dynamic.Heap.Reads heap location cell)
    (cellType : cell.type = FunctionValues.sourceType function)
    (member : Member headers keys registry faults mapping world function native bindings parameter result)
    (written : Dynamic.Heap.Writes heap location (some (.closure function)) after) :
    ∃ updated, store.write? target (.inRight .unit native) = some updated ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
        (CallableIndexedOwnedGeneralLambdaValues.model headers keys registry faults profile)
        mapping world after updated ∧
      AdministrativePreserved mapping store mapping updated ∧
      Dynamic.HeapMetadataExtend heap after ∧
      StoredAt headers keys registry faults mapping world after updated location function native bindings parameter result := by
  have represented : ValueRep compiled.compatible.checked registry
      (CallableIndexedOwnedGeneralLambdaValues.model headers keys registry faults profile)
      mapping world cell.type (.closure function) native (CallableContract.functionType parameter result) :=
    cellType.symm ▸ payload_member profile member
  obtain ⟨updated, coreWritten, finalHeaps, administrative⟩ :=
    GenericHeap.HeapRepresents.write_initialized heaps reference read represented written
  obtain ⟨old, _oldValue, _oldPayload, oldRead, _, _, oldRelated⟩ := heaps.cells reference.mapped
  have same := oldRead.functional read
  subst old
  have ordinary := oldRelated.ordinary
  obtain ⟨previous, previousRead, afterRead⟩ := written.reads_updated
  have same := previousRead.functional read
  subst previous
  have initialized : Dynamic.Heap.Reads after location
      ⟨FunctionValues.sourceType function, some (.closure function), none⟩ := by
    simpa only [cellType, ordinary] using afterRead
  exact ⟨updated, coreWritten, finalHeaps, administrative, .of_write written,
    member, target, reference, initialized, Store.write?_reads_written coreWritten⟩

/-- Source/native writes to a different mapped cell retain this same member
and its actual reads. Injectivity derives distinct physical targets; a frame
preservation receipt alone does not protect mapped payloads. -/
theorem preserves_other
    {heap after : Dynamic.Heap} {store updated : Store}
    {location other : Dynamic.Location} {target : Core.Location} {payload : Ty}
    {replacement : Option Dynamic.Value} {replacementNative : Core.Value}
    (injective : LocationMap.Injective mapping)
    (reference : ReferenceRepresents mapping world location target payload)
    (stored : StoredAt headers keys registry faults mapping world heap store other function native bindings parameter result)
    (different : other ≠ location)
    (written : Dynamic.Heap.Writes heap location replacement after)
    (coreWritten : store.write? target replacementNative = some updated) :
    StoredAt headers keys registry faults mapping world after updated other function native bindings parameter result := by
  obtain ⟨member, otherTarget, otherReference, sourceRead, nativeRead⟩ := stored
  have differentIndices : other.index ≠ location.index := by
    intro same
    apply different
    cases other
    cases location
    simp_all
  have differentTargets : otherTarget ≠ target := by
    intro same
    exact differentIndices (injective (same ▸ otherReference.mapped) reference.mapped)
  exact ⟨member, otherTarget, otherReference, written.preserves_other different sourceRead,
    (Store.write?_preserves_other coreWritten differentTargets).trans nativeRead⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualStoredClosureWriteReceipts
