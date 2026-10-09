import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedChosenOrdinaryLambdaValues
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOrdinaryStoredMembers

/-! Actual initialized writes and allocations retain the chosen receiving model
and the same positive stored member. The generic producers run once; forward
forgetting of the function model is unnecessary at the heap boundary. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedChosenOrdinaryStoredPosts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedNamedGeneration
open CallableIndexedOwnedFunctionValues (Header Key)
open CallableIndexedOwnedPreparedRuntimeFamilyMembers (OrdinaryIndex)
open CallableIndexedOwnedContextualCompilerPolicyProfiles (RootPolicyReceipt)
open CallableIndexedOwnedChosenOrdinaryStoredMembers (ChosenAt ChosenStoredAt extendIndex)
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {caller : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
  {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
  {compilation : Compilation compiled.indexed caller.named diagnostics namedCode}
  {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
  {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
  (root : RootPolicyReceipt (compiled := compiled) caller.named diagnostics namedCode compilation
    rootFuel rootSource rootScope rootId rootReasonAt rootLowered)
  (expressionSyntax : TypedSource → ExpressionId → Prop)
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {i : OrdinaryIndex compiled} {history : History i.code}

/-- The literal constructor supplies the payload relation in the chosen model. -/
theorem payload_member
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    (member : ChosenAt root expressionSyntax headers keys registry faults i history) :
    ValueRep compiled.compatible.checked registry
      (CallableIndexedOwnedChosenOrdinaryLambdaValues.model root expressionSyntax headers keys registry faults profile)
      i.mapping i.world (FunctionValues.sourceType i.function) (.closure i.function)
      (value i.code i.captured.embedding history.native i.capturedActual)
      (CallableContract.functionType i.code.receipt.parameterCore i.code.receipt.resultCore) :=
  .function (.chosen_ordinary i history member)

/-- One actual write preserves the chosen heap relation and the known payload. -/
theorem written_chosen_member
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    {heap after : Dynamic.Heap} {store : Store} {location : Dynamic.Location}
    {target : Location} {cell : Dynamic.Cell}
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
      (CallableIndexedOwnedChosenOrdinaryLambdaValues.model root expressionSyntax headers keys registry faults profile)
      i.mapping i.world heap store)
    (reference : ReferenceRepresents i.mapping i.world location target (CallableContract.functionType i.code.receipt.parameterCore i.code.receipt.resultCore))
    (read : Dynamic.Heap.Reads heap location cell) (cellType : cell.type = (FunctionValues.sourceType i.function))
    (member : ChosenAt root expressionSyntax headers keys registry faults i history)
    (written : Dynamic.Heap.Writes heap location (some (.closure i.function)) after) :
    ∃ updated, store.write? target (.inRight .unit (value i.code i.captured.embedding history.native i.capturedActual)) = some updated ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
        (CallableIndexedOwnedChosenOrdinaryLambdaValues.model root expressionSyntax headers keys registry faults profile)
        i.mapping i.world after updated ∧
      AdministrativePreserved i.mapping store i.mapping updated ∧
      Dynamic.HeapMetadataExtend heap after ∧
      ChosenStoredAt root expressionSyntax headers keys registry faults i history after updated location := by
  have represented : ValueRep compiled.compatible.checked registry
      (CallableIndexedOwnedChosenOrdinaryLambdaValues.model root expressionSyntax headers keys registry faults profile)
      i.mapping i.world cell.type (.closure i.function)
      (value i.code i.captured.embedding history.native i.capturedActual)
      (CallableContract.functionType i.code.receipt.parameterCore i.code.receipt.resultCore) :=
    cellType.symm ▸ payload_member root expressionSyntax profile member
  obtain ⟨updated, writtenCore, finalHeaps, administrative⟩ :=
    GenericHeap.HeapRepresents.write_initialized heaps reference read represented written
  obtain ⟨old, oldValue, oldPayload, oldRead, _, _, oldRelated⟩ := heaps.cells reference.mapped
  have same := oldRead.functional read
  subst old
  have ordinary := oldRelated.ordinary
  obtain ⟨previous, previousRead, afterRead⟩ := written.reads_updated
  have same := previousRead.functional read
  subst previous
  have initialized : Dynamic.Heap.Reads after location
      ⟨FunctionValues.sourceType i.function, some (.closure i.function), none⟩ := by
    simpa only [cellType, ordinary] using afterRead
  exact ⟨updated, writtenCore, finalHeaps, administrative, .of_write written,
    member, target, reference, initialized, Store.write?_reads_written writtenCore⟩

open CallableIndexedHistory CallableIndexedAllocationCompletion

theorem allocated_chosen_member
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    {layouts : SourceCoreAllocationLayouts.Prepared}
    {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {request : SourceCoreSourceCells.Request} {layout : SourceCoreCallableIndexedFrames.Layout}
    {globals : Nat} {allocate : SourceCoreSourceCells.Allocator}
    (allocation : SourceCoreAllocationLayouts.Allocation layouts owner active request)
    (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated layout globals allocate request)
    (same : annotation.original = allocation.expression)
    (definitions : layouts.definitions = compiled.indexed.layouts.definitions)
    (frameRegistered : layout.Registered compiled.indexed.layouts.definitions)
    {administrative : Core.Context} {environment : Dynamic.Environment} {canonical actual : Environment}
    {before after : Dynamic.Heap} {store : Store} {contextLocation : Location}
    {frame : NativeFrame} {sourceLocation : Dynamic.Location}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      i.mapping i.world administrative request.scope environment canonical compiled.indexed.layouts.definitions)
    (agrees : EnvironmentsAgree request.references canonical actual)
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
      (CallableIndexedOwnedChosenOrdinaryLambdaValues.model root expressionSyntax headers keys registry faults profile)
      i.mapping i.world before store)
    (reference : actual[SourceCoreCallableIndexedAllocationFrames.referenceIndex globals request]? =
      some (.cellRef layout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode layout frame))
    (payloadAt : PayloadAt request actual (some (value i.code i.captured.embedding history.native i.capturedActual)))
    (payloadType : request.payloadType = (CallableContract.functionType i.code.receipt.parameterCore i.code.receipt.resultCore))
    (member : ChosenAt root expressionSyntax headers keys registry faults i history)
    (allocated : Dynamic.Heap.Allocates before (FunctionValues.sourceType i.function) (some (.closure i.function)) sourceLocation after) :
    ∃ captured,
      Captures actual request.references request.scope captured ∧
      RuntimeValueHasType i.world captured (SourceCoreSourceCells.captureType request.scope) compiled.indexed.layouts.definitions ∧
      Evaluates actual store annotation.expression
        (.cellRef (OptionalCell.cellType request.payloadType) (store.length + 2))
        (store ++ [SourceCoreCallableIndexedFrames.encode layout frame,
          SourceCoreHeapMarkers.markerValue allocation.entry.layout captured, .inRight .unit (value i.code i.captured.embedding history.native i.capturedActual)]) ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
        (CallableIndexedOwnedChosenOrdinaryLambdaValues.model root expressionSyntax headers keys registry faults profile)
        (i.mapping ++ [store.length + 2])
        (i.world ++ [layout.type, allocation.entry.layout.type, OptionalCell.cellType request.payloadType])
        after (store ++ [SourceCoreCallableIndexedFrames.encode layout frame,
          SourceCoreHeapMarkers.markerValue allocation.entry.layout captured, .inRight .unit (value i.code i.captured.embedding history.native i.capturedActual)]) ∧
      ReferenceRepresents (i.mapping ++ [store.length + 2])
        (i.world ++ [layout.type, allocation.entry.layout.type, OptionalCell.cellType request.payloadType])
        sourceLocation (store.length + 2) request.payloadType ∧
      AdministrativePreserved i.mapping store (i.mapping ++ [store.length + 2])
        (store ++ [SourceCoreCallableIndexedFrames.encode layout frame,
          SourceCoreHeapMarkers.markerValue allocation.entry.layout captured, .inRight .unit (value i.code i.captured.embedding history.native i.capturedActual)]) ∧
      ChosenStoredAt root expressionSyntax headers keys registry faults
        (extendIndex i (futureMap := i.mapping ++ [store.length + 2])
          (futureWorld := i.world ++ [layout.type, allocation.entry.layout.type, OptionalCell.cellType request.payloadType])
          ⟨_, rfl⟩ ⟨_, rfl⟩) history after
        (store ++ [SourceCoreCallableIndexedFrames.encode layout frame,
          SourceCoreHeapMarkers.markerValue allocation.entry.layout captured,
          .inRight .unit (value i.code i.captured.embedding history.native i.capturedActual)]) sourceLocation := by
  have represented : ValueRep compiled.compatible.checked registry
      (CallableIndexedOwnedChosenOrdinaryLambdaValues.model root expressionSyntax headers keys registry faults profile)
      i.mapping i.world (FunctionValues.sourceType i.function) (.closure i.function)
      (value i.code i.captured.embedding history.native i.capturedActual) request.payloadType :=
    payloadType.symm ▸ payload_member root expressionSyntax profile member
  have cell : GenericHeap.CellRepresents
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedChosenOrdinaryLambdaValues.model root expressionSyntax headers keys registry faults profile))
      i.mapping i.world ⟨FunctionValues.sourceType i.function, some (.closure i.function), none⟩
      (optionalValue request.payloadType (some (value i.code i.captured.embedding history.native i.capturedActual)))
      request.payloadType := .initialized represented
  obtain ⟨captured, selected, typed, evaluated, finalHeaps, finalReference, administrative⟩ :=
    CallableIndexedOrdinaryAllocation.preserves_with_captures_for_type allocation annotation same definitions
      frameRegistered environments agrees heaps reference read payloadAt cell allocated
  have maps : LocationMap.Extends i.mapping (i.mapping ++ [store.length + 2]) := ⟨_, rfl⟩
  have worlds : WorldExtends i.world
      (i.world ++ [layout.type, allocation.entry.layout.type, OptionalCell.cellType request.payloadType]) := ⟨_, rfl⟩
  have actualStored : ChosenStoredAt root expressionSyntax headers keys registry faults
      (extendIndex i maps worlds) history after
      (store ++ [SourceCoreCallableIndexedFrames.encode layout frame,
        SourceCoreHeapMarkers.markerValue allocation.entry.layout captured,
        .inRight .unit (value i.code i.captured.embedding history.native i.capturedActual)]) sourceLocation := by
    refine ⟨ChosenAt.extend root expressionSyntax member maps worlds,
      store.length + 2, ?_, allocated.reads_new, ?_⟩
    · exact payloadType ▸ finalReference
    · simp [Store.read?] <;> rfl
  exact ⟨captured, selected, typed, evaluated, finalHeaps, finalReference, administrative, actualStored⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedChosenOrdinaryStoredPosts
