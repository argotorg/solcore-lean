import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageClosureSourceTrace
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageNamedInvocationLifting
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageClosureEntryLifting
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalBranchingLambdaBodyBounds

/-! Real captured closure parameters allocate the original Source environment
and its physical frame before the selected body lift is used. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1800000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageClosureEntryApplicationLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CoreProof CompatiblePayload
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open CallableIndexedOwnedSourceAdmission
open SourceCoreCallableIndexedFrames
open Staging.Recursive
open SelectedCompilationStageClosureEntryLifting (EntryLiftsBelow)
open SelectedCompilationStageBodyLiftBounds (BodyLift)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}   {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
  {mapping : LocationMap} {world : StoreTyping} {capturedActual : Environment}
  (captured : Captures compiled.indexed mapping world scope function.captured capturedActual)
  (code : Code compiled.indexed function scope captured.administrative) (history : History code)
  (inputs : CallableIndexedLambdaEntryPrefix.Context (values := .initial compiled.compatible.checked) code)
  (functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry} {stages : Registry}
  {arguments : List Dynamic.Value} {nativeArguments : List Value}
  (represented : CallableIndexedParameterMeaning.Arguments
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
    mapping world code.receipt.loweredParameters arguments nativeArguments)
  {before : Dynamic.Heap} {store : Store} {callerScope : SourceCoreLocalCell.Scope} {callerCanonical : Environment}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (caller : State headers keys ⟨callerScope, mapping, world, before, store, callerCanonical⟩)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions
    mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before function.context.locals function.captured)
  (reference : captured.canonical[code.referenceIndex]? =
    some (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation))
  {currentMetadata : Option MetadataState}
  (currentCarried : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
    (caller.rows owner.position).authority.current (caller.rows owner.position).authority.ghost currentMetadata)
  (allowed : SourceCoreCallableAncestryPairedPreparation.lambdaAllowed compiled.indexed.ancestry.graph.inputs
    history.metadata code.descriptor.id = true)
  (capturedSlots : CallableIndexedOwnedPhysicalGlobals.Slots compiled
    code.compilation.administrativePrefix scope captured.canonical)
  (physical : CallableIndexedOwnedPhysicalGlobals.Authority compiled mapping store)
  (savedRows : CallableIndexedOwnedIndirectExpressionHeads.StableRows caller)
  (beforeTyped : Dynamic.HeapWellTyped function.context before)
  (argumentsTyped : Dynamic.ValuesHaveTypes function.context before arguments inputs.types)

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions
local notation "canonicalBridge" => CallableIndexedOwnedNamedCallerProtocol.Carrier.forgetSlots
  (CallableIndexedOwnedPhysicalCanonicalState.caller (headers := headers) (keys := keys) code.compilation.administrativePrefix)

private theorem capturedSlots_after_prefix
    {bindings : List CallableIndexedParameterCertificates.Binding}
    {callerPrefix : Nat} {scope : SourceCoreLocalCell.Scope} {canonical : Environment}
    (slots : CallableIndexedOwnedPhysicalGlobals.Slots compiled callerPrefix scope canonical)
    (added : Environment) (length : added.length = bindings.length)
    {final : Environment} (spine : final = added ++ canonical) :
    CallableIndexedOwnedPhysicalGlobals.Slots compiled callerPrefix
      (bindings.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope) final := by
  subst final
  intro slot signature found
  have offset : (bindings.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope).length + callerPrefix + slot =
      added.length + (scope.length + callerPrefix + slot) := by simp only [List.length_append, List.length_map, List.length_reverse]; omega
  rw [offset, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]
  exact slots slot signature found


include represented heaps locals reference currentCarried allowed capturedSlots physical savedRows beforeTyped argumentsTyped in
theorem lifts_application {child invocation : Scope} (selected : stages.Closure function child)
    {callContext : SourceSemantics.Context} {callerEvidence invocationEvidence : Dynamic.EvidenceEnvironment}
    (budget : Nat)
    (bodies : EntryLiftsBelow (headers := headers) (keys := keys) code inputs model stages child budget)
    {size : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.CallOutcome (Program.ofChecked compiled.sourceProgram) size
      callContext callerEvidence invocationEvidence before (.closure function) arguments outcome after)
    (within : size ≤ budget) :
    Lifting.ApplicationLift (Program.ofChecked compiled.sourceProgram) stages invocation callContext before
      (.closure function) arguments outcome after := by
  have arity : function.parameters.length = arguments.length := by
    rw [CallableIndexedLambdaEntryPrefix.parameters (values := .initial compiled.compatible.checked) code,
      List.length_map]
    exact represented.length.1
  obtain ⟨childSize, environment, bound, valid, allocated, sourceTrace, smaller⟩ :=
    SelectedCompilationStageClosureSourceTrace.source_prefix inputs.extended arity trace
  obtain ⟨finalContext, bodyOutcome, bodyTrace, converted⟩ :=
    SelectedCompilationStageNamedInvocationLifting.body_control sourceTrace
  obtain ⟨entry, added, length, spine, parameterState, _parameterRelated⟩ :=
    CallableIndexedOwnedLambdaInvocationBounds.parameters_with_state captured code history inputs
      functions represented owner caller heaps locals reference currentCarried allowed
  obtain ⟨sameEnvironment, sameHeap⟩ := FunctionCallBody.allocations_same entry.entry.allocation allocated
  rw [← sameEnvironment, ← sameHeap] at bodyTrace
  have admitted := CallableIndexedOwnedPreparedLambdaParameterAdmission.at_parameters
    captured code history inputs functions owner caller entry parameterState valid beforeTyped argumentsTyped savedRows
  have slots := capturedSlots_after_prefix capturedSlots added length spine
  let initial : (CallableIndexedOwnedPhysicalCanonicalState.protocol headers keys code.compilation.administrativePrefix).State
      ⟨code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
        entry.entry.mapping, entry.entry.world, entry.entry.heap, entry.entry.store, entry.entry.canonical⟩ :=
    ⟨⟨parameterState, slots⟩,
      (physical.install (frameLocation := owner.key.frameLocation)
        (native := (caller.rows owner.position).authority.current) entry.currentRead entry.next).extend entry.entry.frame⟩
  have canonicalAdmitted : Admission canonicalBridge inputs.context initial := ⟨admitted.heap, admitted.rows⟩
  have conditioned := CallableIndexedOwnedAllocationProducer.stableOwner_selected owner.position entry.nextHistory
  have lifted := bodies entry.entry.environments entry.entry.heaps entry.entry.locals entry.entry.lookups
    entry.entry.actualTyped entry.entry.reference entry.entry.read entry.entry.unmapped conditioned
    initial canonicalAdmitted valid
    (by simpa only [stages.source selected, stages.evidence selected] using bodyTrace)
    (Nat.le_of_lt (Nat.lt_of_lt_of_le smaller within))
  exact BodyLift.closure selected valid inputs.extended entry.entry.allocation lifted converted

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageClosureEntryApplicationLifting
