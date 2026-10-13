import Solcore.SourceSemantics.CoreLowering.SelectedCompilationNamedAdmission
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedBodyPorts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTerminalNamedInvocationBounds

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1800000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationNamedInvocationBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory SourceCoreCallableIndexedFrames
open CallableIndexedParameterMeaning CallableIndexedOwnedFunctionState
open CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
open CallableIndexedOwnedFunctionValues (Header NamedCapture NamedSourceAt)
open CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts (Receipt)
open CallableIndexedOwnedPreparedStagedNamedEntryBounds (Prefix)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry}
  {scope : SourceCoreLocalCell.Scope} {mapping : LocationMap} {world : StoreTyping}
  {before : Dynamic.Heap} {store : Store} {canonical : Environment}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (caller : State headers keys ⟨scope, mapping, world, before, store, canonical⟩)
  (header : Header compiled (Program.ofChecked compiled.sourceProgram))
  (capture : NamedCapture headers owner.key header mapping world)
  {arguments : List Dynamic.Value} {payloads : List Value}

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions
local notation "poolBridge" => CallableIndexedOwnedBodyRestorationAdmission.bridge (headers := headers) (keys := keys)

variable {row : SourceSpecialization.SpecializedFunction}
  (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
  {instantiation : DeclarationInstantiation}
  (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header)
  {native : SourceCoreGeneralFunctions.CallableContext}
  (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared compiled native)
  (descriptor : SourceCoreCallableContracts.Descriptor native.table (.named header.named.signature.key))
  {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment} {function : Dynamic.GlobalFunction}
  (sourceAt : NamedSourceAt header rawD function)
  {faults : RecursiveStageMeaning.FaultRep}

include functions owner caller header capture prepared aligned stagePrepared descriptor sourceAt in
/-- The actual Header and its authenticated named sidecar construct the body
scope. The native prefix reaches its real allocation state, where the body port
reconstructs the staged body. The original global application and the
literal restored caller are then constructed with its actual final lexical context. -/
theorem reflects_invocation
    (sameLayouts : header.layouts = compiled.indexed.layouts)
    (member : header ∈ headers)
    (certified : SelectedCompilationNamedSourceTyping.Certified header)
    (stable : StableRows caller)
    (heapTyped : Dynamic.HeapWellTyped header.function.context before)
    (argumentsTyped : Dynamic.ValuesHaveTypes header.function.context before arguments header.types)
    (represented : Arguments model mapping world header.bindings arguments payloads)
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions mapping world before store)
    {invocation : Staging.Recursive.Scope} {context : SourceSemantics.Context}
    (supports : Dynamic.TypeContextSupports header.context context)
    (budget : Nat)
    (children : ∀ {child : Staging.Recursive.Scope},
      (RecursiveNamedPreparedStageScopes.registry stagePrepared).Closure header.function child →
      CallableIndexedOwnedPreparedStagedNamedBodyPorts.ReflectsBelow (headers := headers) (keys := keys)
        header model
        (RecursiveNamedPreparedStageScopes.registry stagePrepared) child faults budget)
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size (DataPatternValues.packValues payloads :: capture.captured) store
      (header.code.rename capture.embedding.lift) value finalStore)
    (within : size ≤ budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram)
        (RecursiveNamedPreparedStageScopes.registry stagePrepared) sourceSize invocation context before
        (.global function) arguments outcome after ∧
      CallableIndexedOwnedPreparedStagedTerminalNamedInvocationBounds.ResultAt (registry := registry) (payloads := payloads) functions owner caller header capture
        context outcome after value finalStore finalMap finalWorld faults := by
  obtain ⟨packet⟩ := CallableIndexedOwnedPreparedStagedNamedEntryBounds.native_prefix
    (functions := functions) (registry := registry) owner caller header capture sameLayouts member represented heaps completed
  let receipt := CallableIndexedOwnedPreparedStagedTerminalNamedInvocationBounds.parameter_receipt functions owner caller header capture packet stable heapTyped argumentsTyped
  have source := SelectedCompilationNamedAdmission.parameter_source certified receipt.body.allocation receipt.heapTyped receipt.argumentsTyped
  obtain ⟨sidecar, _issued, _same, globalSelected, _declaration, _local, _evidence, _return, _analysis⟩ :=
    CallableIndexedOwnedPreparedStagedNamedSourceScopeReceipts.selected sourceAt prepared aligned stagePrepared descriptor
  have selected : (RecursiveNamedPreparedStageScopes.registry stagePrepared).Closure header.function
      (RecursiveStageRegistry.scope sidecar [] header.function) := by
    rw [CallableIndexedOwnedPreparedStagedNamedSourceScopeReceipts.global_view sourceAt] at globalSelected
    exact globalSelected
  have admitted : Admission poolBridge header.context packet.reached :=
    ⟨source.heapTyped, receipt.rows⟩
  obtain ⟨sourceSize, finalContext, bodyOutcome, outcome, after, finalMap, finalWorld, trace, matched, result,
    finalHeaps, bodyMaps, bodyWorlds, bodyFrame, bodyMetadata, bodyState, bodyRelated, bodyPost⟩ :=
    children selected packet.entry.environments packet.entry.heaps packet.entry.locals
      packet.entry.lookups packet.entry.actualTyped packet.reached admitted owner
      (fun zero globals => receipt.packet zero globals)
      packet.completed (Nat.le_of_lt (Nat.lt_of_lt_of_le packet.strict within))
  have applied := CallableIndexedOwnedPreparedStagedNamedSourceScopeReceipts.applies
    (caller := invocation) (context := context) sourceAt stagePrepared selected
    header.extended packet.entry.allocation trace matched
  have maps := packet.entry.maps.trans bodyMaps
  have worlds := packet.entry.worlds.trans bodyWorlds
  have frame := packet.entry.frame.trans bodyFrame
  have metadata := packet.entry.metadata.trans bodyMetadata
  have related : Relates caller bodyState := packet.related.trans bodyRelated
  have physical : (caller.rows owner.position).authority.frameLocation = keys[owner.position.val].frameLocation :=
    (caller.rows owner.position).frame_eq
  obtain ⟨restoredHeaps, restoredFrame, _cell, _fromBody, restoredRelated, _records, _transition⟩ :=
    CallableIndexedOwnedBodyRestoration.restore_return caller bodyState owner.position header.registered finalHeaps worlds
      (by simpa only [physical] using frame) related
  have restoredPost := CallableIndexedOwnedPreparedStagedBodyRestorationAdmission.restore_post
    caller bodyState owner.position stable bodyPost supports restoredFrame
  have storeEq : finalStore = (CallableIndexedOwnedBodyRestoration.finalIndex (body :=
      ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)),
        finalMap, finalWorld, after, packet.bodyStore, packet.entry.canonical⟩) caller owner.position).store := by
    simpa only [CallableIndexedOwnedBodyRestoration.finalIndex, ← physical] using packet.restored
  have whole := completed.sound
  rw [storeEq] at whole
  refine ⟨Staging.Recursive.Size.stepSize [sourceSize], outcome, after, finalMap, finalWorld, applied, ?_⟩
  rw [storeEq]
  exact ⟨whole, result, restoredHeaps, maps, worlds, restoredFrame, metadata,
    CallableIndexedOwnedBodyRestoration.returned caller bodyState owner.position, restoredRelated, restoredPost⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationNamedInvocationBounds
