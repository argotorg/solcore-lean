import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageBodyLiftBounds
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalNamedInvocationPreservation
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedSourceScopeReceipts

/-! An ordinary named invocation enters the same authenticated physical
parameter frame. The selected body lift retains its exact captured state. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1800000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageNamedInvocationLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory SourceCoreCallableIndexedFrames
open CallableIndexedParameterCertificates CallableIndexedParameterMeaning RecursiveNamedCatalog
open RecursiveNamedCatalogInvocationBounds CallableIndexedOwnedFunctionState
open CallableIndexedOwnedInvocationBounds CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
open CallableIndexedOwnedFunctionValues (Header NamedCapture NamedSourceAt)
open SelectedCompilationStageBodyLiftBounds (NamedLiftsBelow BodyLift)
open Staging.Recursive.Lifting (ApplicationLift)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}

theorem source_prefix
    {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
    {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment} {function : Dynamic.GlobalFunction}
    (sourceAt : NamedSourceAt header rawD function)
    (owners : ((Program.ofChecked compiled.sourceProgram).functions.map (fun definition => definition.body.owner)).Nodup)
    {context : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    {before after : Dynamic.Heap} {arguments : List Dynamic.Value} {outcome : Dynamic.ExpressionOutcome} {size : Nat}
    (arity : header.function.parameters.length = arguments.length)
    (trace : RecursiveNamedCallBounds.CallOutcome (Program.ofChecked compiled.sourceProgram) size
      context callerEvidence function.evidence before (.global function) arguments outcome after) :
    ∃ bodySize environment bound,
      Dynamic.BindersAllocate [] before header.function.parameters arguments environment bound ∧
      RecursiveNamedCallBounds.BodyTrace (Program.ofChecked compiled.sourceProgram) bodySize
        header.function header.context environment bound outcome after ∧ bodySize < size := by
  have canonical : RecursiveNamedCallBounds.CallOutcome (Program.ofChecked compiled.sourceProgram) size
      context callerEvidence header.function.evidence before
      (.global ⟨function.instantiation, header.function.evidence⟩) arguments outcome after := by
    simpa only [sourceAt.dictionary] using trace
  obtain ⟨bodySize, bodyTrace, bodySmaller⟩ := RecursiveNamedCallBounds.source_call_body
    owners sourceAt.frame arity canonical
  obtain ⟨childSize, environment, bound, allocated, statements, smaller⟩ :=
    RecursiveNamedCallBounds.body_trace sourceAt.frame header.extended arity bodyTrace
  exact ⟨childSize, environment, bound, allocated, statements, Nat.lt_trans smaller bodySmaller⟩

theorem body_control {program : Program} {function : Dynamic.Closure} {size : Nat}
    {context : SourceSemantics.Context} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {outcome : Dynamic.ExpressionOutcome}
    (trace : RecursiveNamedCallBounds.BodyTrace program size function context environment before outcome after) :
    ∃ finalContext control,
      RecursiveNamedCallBounds.FunctionOutcome program size context function.evidence function.source
        environment before function.body finalContext control after ∧
      CompatibleNamedBody.Exit function.resultType control outcome := by
  cases trace with
  | returned execution => exact ⟨_, _, .control execution, .returned _⟩
  | unit same execution => exact ⟨_, _, .control execution, .unit _ same⟩
  | fault failed => exact ⟨_, _, .fault failed, .fault _⟩
  | escaped execution escape =>
    rcases escape with ⟨environment, rfl⟩ | ⟨environment, rfl⟩
    · exact ⟨_, _, .control execution, .breaking environment⟩
    · exact ⟨_, _, .control execution, .continuing environment⟩

private theorem related_cast_frame
    {initial : ProtectedStateTransition.Index} (saved : State headers keys initial)
    {scope : SourceCoreLocalCell.Scope} {canonical : Environment}
    {first second : Location} {next : Value} (same : first = second)
    (state : State headers keys ⟨scope, mapping, world, heap, store.set first next, canonical⟩)
    (related : Relates saved state) :
    Relates saved (Eq.mp (congrArg (fun location => State headers keys
      ⟨scope, mapping, world, heap, store.set location next, canonical⟩) same) state) := by
  cases same
  exact related

private theorem readyAt_cast
    {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment}
    {model : GenericHeap.PayloadModel catalog projects definitions}
    {first second : SourceCoreAllocationLayouts.Prepared}
    {frame : SourceCoreCallableIndexedFrames.Layout}
    (same : first = second)
    (producer : ProtectedStateTransition.MarkedAllocation.Producer (protocol headers keys) second frame model)
    {location : Location} {native : NativeFrame}
    (ready : ProtectedStateTransition.OrdinaryAllocation.ReadyAt producer.toOrdinary location native) :
    ProtectedStateTransition.OrdinaryAllocation.ReadyAt
      ((same.symm ▸ producer).toOrdinary) location native := by
  cases same
  exact ready
variable
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry}
  {scope : SourceCoreLocalCell.Scope} {canonical : Environment}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (caller : State headers keys ⟨scope, mapping, world, heap, store, canonical⟩)
  (header : Header compiled (Program.ofChecked compiled.sourceProgram))
  (physicalCapture : CallableIndexedOwnedNamedPhysicalCaptures.Capture headers owner.key header mapping world store)
variable {arguments : List Dynamic.Value} {payloads : List Value}
  {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment} {function : Dynamic.GlobalFunction}
  (sourceAt : NamedSourceAt header rawD function)

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions
local notation "poolBridge" => CallableIndexedOwnedBodyRestorationAdmission.bridge (headers := headers) (keys := keys)


include functions owner caller header physicalCapture sourceAt in
theorem lifts_invocation
    (sameLayouts : header.layouts = compiled.indexed.layouts)
    (physicalAuthority : CallableIndexedOwnedPhysicalGlobals.Authority compiled mapping store)
    (member : header ∈ headers)
    (owners : ((Program.ofChecked compiled.sourceProgram).functions.map (fun definition => definition.body.owner)).Nodup)
    (certified : SelectedCompilationNamedSourceTyping.Certified header)
    (stable : StableRows caller)
    (heapTyped : Dynamic.HeapWellTyped header.function.context heap)
    (argumentsTyped : Dynamic.ValuesHaveTypes header.function.context heap arguments header.types)
    (represented : Arguments model mapping world header.bindings arguments payloads)
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions mapping world heap store)
    {stages : Staging.Recursive.Registry} {invocation child : Staging.Recursive.Scope}
    {context : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    (selected : stages.Closure header.function child)
    (budget : Nat)
    (children : NamedLiftsBelow (headers := headers) (keys := keys) header model stages child budget)
    {size : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.CallOutcome (Program.ofChecked compiled.sourceProgram)
      size context callerEvidence function.evidence heap (.global function) arguments outcome after)
    (within : size ≤ budget) :
    ApplicationLift (Program.ofChecked compiled.sourceProgram) stages invocation context heap
      (.global function) arguments outcome after := by
  let authority := (caller.rows owner.position).authority
  have physical : authority.frameLocation = owner.key.frameLocation := (caller.rows owner.position).frame_eq
  change authority.frameLocation = keys[owner.position.val].frameLocation at physical
  have liveLocals : Dynamic.EnvironmentAgrees heap header.function.context.locals [] := by
    obtain ⟨original⟩ := CallableIndexedOwnedFunctionEntries.capture_from_pool caller owner member
    exact original.locals
  have liveReference : (physicalCapture.named).canonical[header.globals]? =
      some (.cellRef compiled.indexed.ancestry.layout.frame.type authority.frameLocation) := by
    simpa only [physical, CallableIndexedOwnedFunctionValues.OwnedKey.key] using (physicalCapture.named).reference
  have arity : header.function.parameters.length = arguments.length := by
    rw [header.parameters, List.length_map]; exact represented.length.1
  obtain ⟨childSize, environment, bound, allocated, sourceTrace, smaller⟩ :=
    source_prefix sourceAt owners arity trace
  obtain ⟨finalContext, bodyOutcome, bodyTrace, converted⟩ := body_control sourceTrace
  obtain ⟨origin, index, metadata, owned, history, emitted⟩ :=
    CallableIndexedFormation.namedBody_history compiled.indexed.ancestry header.hook
  let installed := CallableIndexedOwnedFunctionState.install caller owner.position (.stable history)
  let installedAuthority := authority.install (.stable history)
  have installedHeaps := (CallableIndexedBodyFrames.install header.registered heaps authority.unmapped authority.typed
    authority.frame (.stable history)).1
  have layout : EnvironmentsAgree
      (Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) (physicalCapture.named).embedding.lift))
      (DataPatternValues.packValues payloads :: (physicalCapture.named).canonical)
      (.unit :: encode compiled.indexed.ancestry.layout.frame authority.current :: DataPatternValues.packValues payloads :: (physicalCapture.named).captured) :=
    GenericExpressionMeaning.agree_prefix
      (GenericExpressionMeaning.agree_prefix (ReadOnly.EnvironmentsAgree.lift (physicalCapture.named).layout (DataPatternValues.packValues payloads))
        (encode compiled.indexed.ancestry.layout.frame authority.current)) .unit
  have packTyped : RuntimeValueHasType world (DataPatternValues.packValues payloads)
      header.named.signature.parameterType (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions :=
    header.parameterType.symm ▸ CallableIndexedParameters.Arguments.pack_typed represented
  have actualTyped := RuntimeEnvironmentHasTypes.cons
    (RuntimeValueHasType.unit (definitions := (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions))
    (.cons (encode_runtime_typed world header.registered authority.current) (.cons packTyped (physicalCapture.named).typed))
  let producer : ProtectedStateTransition.MarkedAllocation.Producer (protocol headers keys)
      header.layouts compiled.indexed.ancestry.layout.frame model :=
    sameLayouts.symm ▸ CallableIndexedOwnedMarkedAllocation.producer headers keys model
  have readyAt : ProtectedStateTransition.OrdinaryAllocation.ReadyAt producer.toOrdinary authority.frameLocation (.state index) := by
    exact readyAt_cast sameLayouts _ (CallableIndexedOwnedAllocationProducer.readyAt_of_owner_eq
      model owner.position physical.symm history)
  let parameterInitial : State headers keys
      ⟨[], mapping, world, heap, store.set authority.frameLocation (encode compiled.indexed.ancestry.layout.frame (.state index)), (physicalCapture.named).canonical⟩ :=
    Eq.mp (congrArg (fun location => State headers keys
      ⟨[], mapping, world, heap, store.set location (encode compiled.indexed.ancestry.layout.frame (.state index)), (physicalCapture.named).canonical⟩)
      physical.symm) installed
  obtain ⟨entry, parameterTransition, agreement, spine⟩ :=
    CallableIndexedOwnedPreparedStagedPhysicalNamedEntryBounds.parameters_with_state_spine installedAuthority
    (physicalCapture.named).environments liveLocals liveReference (physicalCapture.named).coherent represented installedHeaps
    layout actualTyped producer parameterInitial readyAt
  obtain ⟨parameterState, parameterRelated⟩ := parameterTransition
  obtain ⟨sameEnvironment, sameHeap⟩ := FunctionCallBody.allocations_same entry.allocation allocated
  rw [← sameEnvironment, ← sameHeap] at bodyTrace
  have installedRelated : Relates caller parameterInitial := by
    exact related_cast_frame caller physical.symm installed
      (CallableIndexedOwnedFunctionState.install_related caller owner.position (.stable history))
  let receipt : CallableIndexedOwnedPreparedNamedParameterReceipts.Receipt (registry := registry) functions owner caller header arguments :=
    ⟨origin, index, metadata, (physicalCapture.named).administrative, _,
      .unit :: encode compiled.indexed.ancestry.layout.frame authority.current :: DataPatternValues.packValues payloads :: (physicalCapture.named).captured,
      Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) (physicalCapture.named).embedding.lift),
      authority.frameLocation, (caller.rows owner.position).frame_eq, owned, history, emitted,
      entry, parameterState, installedRelated.trans parameterRelated, stable, heapTyped, argumentsTyped⟩
  have admitted : Admission poolBridge header.context parameterState := ⟨(SelectedCompilationNamedAdmission.parameter_source certified receipt.body.allocation receipt.heapTyped receipt.argumentsTyped).heapTyped, receipt.rows⟩
  have physicalEntry := (physicalAuthority.install authority.frame.read (.state index)).extend entry.frame
  have physicalSlots : CallableIndexedOwnedPhysicalGlobals.Slots compiled 1
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) entry.canonical := by
    obtain ⟨added, length, same⟩ := spine
    intro slot signature found
    rw [same]
    have offset : (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))).length + 1 + slot =
        added.length + (slot + 1) := by simp only [List.length_map, List.length_reverse]; omega
    rw [offset, List.getElem?_append_right (by omega)]
    simpa only [Nat.add_sub_cancel_left, List.getElem?_cons_succ, List.length_nil, Nat.zero_add] using physicalCapture.slots slot signature found
  have lifted := children entry.environments entry.heaps entry.locals entry.lookups
    entry.actualTyped parameterState admitted owner
    (fun zero globals => receipt.packet zero globals)
    physicalCapture.keyPhysical physicalEntry physicalSlots
    (by simpa only [stages.source selected, stages.evidence selected] using bodyTrace)
    (Nat.le_of_lt (Nat.lt_of_lt_of_le smaller within))
  have selectedActual : stages.Closure
      (Staging.Recursive.globalView header.sourceBody function.evidence header.function.body) child := by
    simpa only [CallableIndexedOwnedPreparedStagedNamedSourceScopeReceipts.global_view sourceAt] using selected
  have parameters : MonoBindersExtend header.sourceBody.source.owner header.sourceBody.context
      header.sourceBody.source.inputs header.types header.context := by
    simpa only [sourceAt.frame.source, sourceAt.frame.context, sourceAt.frame.parameters] using header.extended
  exact SelectedCompilationStageBodyLiftBounds.BodyLift.global sourceAt.frame.instantiated
    (sourceAt.dictionary ▸ sourceAt.frame.covers) sourceAt.frame.roots selectedActual parameters
    (sourceAt.frame.parameters ▸ entry.allocation) lifted (sourceAt.frame.result ▸ converted)

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageNamedInvocationLifting
