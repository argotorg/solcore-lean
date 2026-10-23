import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaFormationReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPhysicalCellOrigins
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPhysicalLambdaFormation
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedExpressionBounds

/-! Ordinary lambda formation uses the actual named packet and keeps the
same positive closure member in the public receiving model. The retained
Site and body are static compiler receipts; captures come from this input. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedPhysicalLambdaFormationHeads
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedExpressionBounds
open RecursiveNamedLambdaFormationHeads
open CallableIndexedOwnedGeneralOrdinaryLambdaFormationHeads (Formation)
open CallableIndexedOwnedContextualLambdaFormationReceipts (OrdinaryFormation)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry receiving : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  (caller : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (context : SourceSemantics.Context) {stages : Staging.Recursive.Registry}
  (invocation : Staging.Recursive.Scope)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  (globals : caller.globals = compiled.indexed.base.globals.length)
  (slots : ∀ header, header ∈ headers → header.slot < compiled.indexed.base.globals.length)
  (prefixZero : owner.key.capturePrefix = 0)
  (sameSource : invocation.source = CallableIndexedNamedGeneration.source caller.named)

local notation "functions" => CallableIndexedOwnedPhysicalCellOrigins.functions headers keys bodyRegistry semanticFaults profile
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions
local notation "bridge" => CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner caller

abbrev Certificate : GenericExpressionMeaning.Certificate :=
  fun scope id lowered => Nonempty (OrdinaryFormation (registry := bodyRegistry) (faults := semanticFaults)
    caller context invocation.evidence scope id lowered)

include globals slots prefixZero in
theorem forms {scope : SourceCoreLocalCell.Scope} {id : ExpressionId}
    {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : OrdinaryFormation (registry := bodyRegistry) (faults := semanticFaults)
      caller context invocation.evidence scope id lowered)
    {mapping world administrative environment canonical actual actualContext before store ξ}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      mapping world administrative scope environment canonical compiled.indexed.layouts.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked receiving functions mapping world before store)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (nativeTyped : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
    (allSlots : CallableIndexedOwnedPhysicalGlobals.Slots compiled 1 scope canonical)
    (initial : (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner caller).State
      ⟨scope, mapping, world, before, store, canonical⟩) :
    ∃ payload,
      Evaluates actual store (lowered.expression.rename ξ) (.inRight .word payload) store ∧
      ValueRep compiled.compatible.checked receiving functions mapping world
        receipt.site.code.sourceNode.type (.closure (receipt.toFormation.function environment)) payload lowered.type := by
  let head := receipt.toFormation
  let entry := CallableIndexedOwnedLambdaViewHeads.nested_entry initial.val owner prefixZero
    initial.property.observed initial.property.carried initial.property.bundle globals
  let captured := CallableIndexedOwnedPhysicalLambdaCaptures.captures_for allSlots globals entry environments agrees nativeTyped
  have observed := CallableIndexedOwnedPhysicalLambdaCaptures.capture_globals_for allSlots globals slots entry environments agrees nativeTyped
  have observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
      (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
      headers owner.key.locations 1 scope captured.canonical owner.key.frameLocation := by
    change CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
      (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
      headers owner.key.locations 1 scope captured.canonical
      (initial.val.rows owner.position).authority.frameLocation at observed
    rw [(initial.val.rows owner.position).frame_eq] at observed
    exact observed
  have capturedSlots := CallableIndexedOwnedPhysicalLambdaCaptures.capture_slots_for allSlots globals entry environments agrees nativeTyped
  let code : Code compiled.indexed (head.function environment) scope captured.administrative := head.code environment
  let support : CallableIndexedOwnedOrdinaryLambdaSupport.Support code bodyRegistry semanticFaults := head.support environment
  obtain ⟨_sourceTrace, native, _determined, member⟩ :=
    @CallableIndexedOwnedPhysicalLambdaFormation.formation_member compiled headers keys
      bodyRegistry semanticFaults mapping world (head.function environment) scope actual canonical before store
      captured code support owner initial.val initial.property profile rfl observed (receipt.at environment globals)
      capturedSlots heaps.runtime_hasTypes receipt.ordinary receipt.coercions
  have payload := CallableIndexedOwnedPhysicalCellOrigins.payload_static_member (registry := receiving) profile member
  let actualHistory : History code :=
    @CallableIndexedOwnedAdmittedGeneralOrdinaryLambdaFormation.history_at compiled headers keys bodyRegistry
      semanticFaults (head.function environment) scope mapping world before store actual canonical
      captured code support owner initial.val initial.property
  refine ⟨value code captured.embedding actualHistory.native actual, ?_, ?_⟩
  · simpa only [code, Formation.code, recaptureCode, head, receipt.emitted, captured, CallableIndexedOwnedPhysicalLambdaCaptures.captures_for, actualHistory] using native
  have sourceType : receipt.site.code.sourceNode.type = FunctionValues.sourceType (head.function environment) := receipt.sourceType
  have nativeType := CallableIndexedOwnedAdmittedMethodLambdaFormation.native_type
    (compiled := compiled) (function := head.function environment) captured code
  rw [sourceType]
  have emittedType : lowered.type = CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore := by
    simpa only [code, Formation.code, recaptureCode, head, receipt.emitted] using nativeType
  rw [emittedType]
  exact payload

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedPhysicalLambdaFormationHeads
