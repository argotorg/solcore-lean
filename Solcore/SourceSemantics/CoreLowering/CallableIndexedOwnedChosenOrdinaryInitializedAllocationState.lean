import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedChosenOrdinaryStoredPosts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedLexicalAllocation
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMarkedAllocation

/-! One actual initialized marked allocation retains its complete reached caller
state and positively attaches the known chosen closure to the new optional cell.
Raw Source value typing and the compiler binder/payload equations stay explicit. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedChosenOrdinaryInitializedAllocationState
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedNamedGeneration
open CallableIndexedOwnedFunctionValues (Header Key)
open CallableIndexedOwnedPreparedRuntimeFamilyMembers (OrdinaryIndex)
open CallableIndexedOwnedContextualCompilerPolicyProfiles (RootPolicyReceipt)
open CallableIndexedOwnedChosenOrdinaryStoredMembers (ChosenAt ChosenStoredAt extendIndex)
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedAllocationCompletion TypedLexicalControl
universe u
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


variable (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error} {source : TypedSource}

local notation "receiving" => CallableIndexedOwnedChosenOrdinaryLambdaValues.model
  root expressionSyntax headers keys registry faults profile

/-- The positive constructor supplies the payload relation, and the original
stateful producer runs once. Every output belongs to its same allocation tuple. -/
theorem allocate_initialized
    (definitions : layouts.definitions = (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    (registered : frame.Registered (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    (producer : ProtectedStateTransition.MarkedAllocation.Producer callerProtocol layouts frame
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry receiving))
    {context nextContext : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    {binder : TypedBinder} {payload : Ty}
    (mono : binder.scheme.quantified = []) (extended : BinderExtends source.owner context binder nextContext)
    (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
    (allocation : SourceCoreAllocationLayouts.Allocation layouts owner active (initializedRequest source scope binder payload))
    (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated frame globals
      (layouts.allocatorAt owner active onError) (initializedRequest source scope binder payload))
    (same : annotation.original = allocation.expression)
    (binderType : binder.scheme.body = FunctionValues.sourceType i.function)
    (payloadType : payload = CallableContract.functionType i.code.receipt.parameterCore i.code.receipt.resultCore)
    (member : ChosenAt root expressionSyntax headers keys registry faults i history)
    {administrative actualContext : Core.Context} {environment : Dynamic.Environment}
    {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame} {location : Dynamic.Location}
    (valueTyped : Dynamic.ValueHasType context before (.closure i.function) binder.scheme.body)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      i.mapping i.world administrative scope environment canonical (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry receiving i.mapping i.world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes i.world actual actualContext (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (allocated : Dynamic.Heap.Allocates before binder.scheme.body (some (.closure i.function)) location after)
    (initial : callerProtocol.State ⟨scope, i.mapping, i.world, before, store, canonical⟩)
    (ready : producer.Ready initial contextLocation native)
    (admitted : Admission bridge context initial) :
    ∃ captured,
      Captures (value i.code i.captured.embedding history.native i.capturedActual :: canonical)
        (initializedRequest source scope binder payload).references scope captured ∧
      RuntimeValueHasType i.world captured (SourceCoreSourceCells.captureType scope)
        (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions ∧
      let closureValue := value i.code i.captured.embedding history.native i.capturedActual
      let nextStore := store ++ [SourceCoreCallableIndexedFrames.encode frame native,
        SourceCoreHeapMarkers.markerValue allocation.entry.layout captured, .inRight .unit closureValue]
      let nextWorld := i.world ++ [frame.type, allocation.entry.layout.type, OptionalCell.cellType payload]
      let nextMap := i.mapping ++ [store.length + 2]
      let nextRef := Value.cellRef (OptionalCell.cellType payload) (store.length + 2)
      Evaluates (closureValue :: actual) store (annotation.expression.rename ξ.lift) nextRef nextStore ∧
      DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog) nextMap nextWorld administrative
        ((binder.id, payload) :: scope) ((binder.id, location) :: environment) (nextRef :: canonical)
        (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry receiving nextMap nextWorld after nextStore ∧
      Dynamic.EnvironmentAgrees after nextContext.locals ((binder.id, location) :: environment) ∧
      EnvironmentsAgree (Renaming.comp (Renaming.insertion 0) ξ).lift (nextRef :: canonical) (nextRef :: closureValue :: actual) ∧
      RuntimeEnvironmentHasTypes nextWorld (nextRef :: closureValue :: actual)
        (OptionalCell.referenceType payload :: payload :: actualContext)
        (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions ∧
      (nextRef :: canonical)[((binder.id, payload) :: scope).length + 1 + globals]? = some (.cellRef frame.type contextLocation) ∧
      nextStore.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native) ∧
      AdministrativePreserved i.mapping store nextMap nextStore ∧
      ∃ (maps : LocationMap.Extends i.mapping nextMap) (worlds : WorldExtends i.world nextWorld),
        Dynamic.HeapMetadataExtend before after ∧
        ReferenceRepresents nextMap nextWorld location (store.length + 2) payload ∧
        ChosenStoredAt root expressionSyntax headers keys registry faults
          (extendIndex i maps worlds) history after nextStore location ∧
        ∃ reached : callerProtocol.State
            ⟨(binder.id, payload) :: scope, nextMap, nextWorld, after, nextStore, nextRef :: canonical⟩,
          callerProtocol.Relates initial reached ∧
          Relates (bridge.pool initial) (bridge.pool reached) ∧
          Admission bridge nextContext reached := by
  have represented : ValueRep compiled.compatible.checked registry receiving i.mapping i.world
      binder.scheme.body (.closure i.function)
      (value i.code i.captured.embedding history.native i.capturedActual) payload := by
    rw [binderType, payloadType]
    exact CallableIndexedOwnedChosenOrdinaryStoredPosts.payload_member root expressionSyntax profile member
  obtain ⟨captured, captures, capturedTyped, evaluated, nextEnvironments, nextHeaps, nextLocals,
      nextAgrees, nextTyped, nextReference, nextRead, preservation, reached, related, nextAdmission⟩ :=
    CallableIndexedOwnedAdmittedLexicalAllocation.allocate_initialized bridge receiving definitions registered
      producer.toOrdinary mono extended ordinary allocation annotation same valueTyped represented
      environments heaps locals agrees actualTyped reference read allocated initial ready admitted
  have maps : LocationMap.Extends i.mapping (i.mapping ++ [store.length + 2]) := ⟨_, rfl⟩
  have worlds : WorldExtends i.world
      (i.world ++ [frame.type, allocation.entry.layout.type, OptionalCell.cellType payload]) := ⟨_, rfl⟩
  have freshReference : ReferenceRepresents (i.mapping ++ [store.length + 2])
      (i.world ++ [frame.type, allocation.entry.layout.type, OptionalCell.cellType payload])
      location (store.length + 2) payload := by
    refine ⟨?_, ?_⟩
    · rw [allocated.location_fresh, ← heaps.length_eq]
      simp
    · cases nextTyped with
      | cons typed _ =>
        cases typed with
        | cellRef found => exact found
  have stored : ChosenStoredAt root expressionSyntax headers keys registry faults
      (extendIndex i maps worlds) history after
      (store ++ [SourceCoreCallableIndexedFrames.encode frame native,
        SourceCoreHeapMarkers.markerValue allocation.entry.layout captured,
        .inRight .unit (value i.code i.captured.embedding history.native i.capturedActual)]) location := by
    refine ⟨ChosenAt.extend root expressionSyntax member maps worlds, store.length + 2,
      payloadType ▸ freshReference, ?_, ?_⟩
    · change after.Reads location ⟨FunctionValues.sourceType i.function, some (.closure i.function), none⟩
      simpa only [binderType] using allocated.reads_new
    · simp [Store.read?] <;> rfl
  exact ⟨captured, captures, capturedTyped, evaluated, nextEnvironments, nextHeaps,
    nextLocals, nextAgrees, nextTyped, nextReference, nextRead, preservation,
    maps, worlds, .of_allocation allocated, freshReference, stored,
    reached, related, bridge.related related, nextAdmission⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedChosenOrdinaryInitializedAllocationState
