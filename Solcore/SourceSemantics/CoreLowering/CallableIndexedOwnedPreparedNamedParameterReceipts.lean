import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedExpressionHeads
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNamedArgumentAdmission
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedBodyEntries
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNamedCanonicalEntries
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNestedCallerProtocol

/-! An actual named hook and parameter allocation retain their complete input
without a body profile. Source admission and all installed rows concern that
same reached pool. The existing invocation cores receive only a strict body
child at this genuine receipt. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedParameterReceipts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory SourceCoreCallableIndexedFrames
open RecursiveNamedCatalog RecursiveNamedCatalogInvocationBounds
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
open CallableIndexedOwnedAdmittedBodyEntries (SourceReceipt)
open RecursiveNamedBoundedContracts
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)

/-- Every field belongs to the actual hook and parameter producer. Independent
Source typing describes the argument heap before the real allocation. -/
structure Receipt
    {initial : ProtectedStateTransition.Index} (argumentsPool : State headers keys initial)
    (header : CallableIndexedOwnedFunctionValues.Header compiled program) (arguments : List Dynamic.Value) where
  origin : Word
  index : Int
  metadata : MetadataState
  administrative : Core.Context
  actualContext : Core.Context
  actual : Environment
  embedding : Renaming
  frameLocation : Location
  physical : frameLocation = owner.key.frameLocation
  selected : compiled.indexed.ancestry.graph.inputs.callable.table.idAt? (.named header.named.signature.key) = some origin
  history : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
    (.state index) (.named origin) (some metadata)
  emitted : header.code = withFrame (.var (compiled.indexed.base.globals.length + 1))
    (SourceCoreCallableIndexedDispatch.literal compiled.indexed.ancestry.layout.frame (.state index)) header.parameterCode
  body : BodyState (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    headers owner.key.locations owner.key.capturePrefix functions registry header arguments initial.heap
    (initial.store.set frameLocation (encode compiled.indexed.ancestry.layout.frame (.state index)))
    initial.mapping initial.world administrative actualContext actual embedding frameLocation (.state index) (.named origin)
  reached : State headers keys ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)),
    body.mapping, body.world, body.heap, body.store, body.canonical⟩
  related : Relates argumentsPool reached
  stable : StableRows argumentsPool
  heapTyped : Dynamic.HeapWellTyped header.function.context initial.heap
  argumentsTyped : Dynamic.ValuesHaveTypes header.function.context initial.heap arguments header.types

section Observations
variable {functions owner}
  {initial : ProtectedStateTransition.Index} {argumentsPool : State headers keys initial}
  {header : CallableIndexedOwnedFunctionValues.Header compiled program} {arguments : List Dynamic.Value}
  (receipt : Receipt (registry := registry) functions owner argumentsPool header arguments)

/-- Source instantiation and allocation supply the complete actual body seed. -/
theorem Receipt.source (wellFormed : ProgramWellFormed program) :
    SourceReceipt program header.function header.context receipt.body.environment receipt.body.heap :=
  SourceReceipt.of_named wellFormed header.frame header.extended receipt.body.allocation
    receipt.heapTyped receipt.argumentsTyped

/-- The real hook authenticates the complete named Source history. -/
theorem Receipt.allowed :
    CallableIndexedOwnedNamedCanonicalEntries.condition functions owner header receipt.body :=
  CallableIndexedOwnedNamedCanonicalEntries.authorized functions owner header
    receipt.physical receipt.selected receipt.history receipt.emitted receipt.body

/-- The actual parameter catalog retains the original global slots. -/
theorem Receipt.global_slots :
    CallableIndexedOwnedExpressionHeads.Globals (headers := headers) owner (owner.key.capturePrefix + 1)
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) receipt.body.canonical :=
  receipt.body.catalog.globals

/-- The real named history supplies the actual marked-allocation gate. -/
theorem Receipt.stable_owner :
    CallableIndexedOwnedAllocationProducer.StableOwner keys receipt.frameLocation (.state receipt.index) :=
  CallableIndexedOwnedNamedCanonicalEntries.stable_owner functions owner header receipt.body receipt.allowed

/-- Hook installation and the original parameter effects retain every row at
the same reached pool, including repeated physical frame snapshots. -/
theorem Receipt.rows : StableRows receipt.reached := by
  have parameterFrame := Eq.mp (congrArg (fun location => AdministrativePreserved initial.mapping
    (initial.store.set location (encode compiled.indexed.ancestry.layout.frame (.state receipt.index)))
    receipt.body.mapping receipt.body.store) receipt.physical) receipt.body.frame
  exact StableRows.after_administrative
    (CallableIndexedOwnedFunctionState.install argumentsPool owner.position (.stable receipt.history))
    receipt.reached
    (CallableIndexedOwnedAdmittedBodyEntries.stable_rows_install argumentsPool receipt.stable owner.position receipt.history)
    parameterFrame

/-- Real zero-prefix and global-count receipts produce the principal packet
beside this exact reached pool. -/
theorem Receipt.packet (prefixZero : owner.key.capturePrefix = 0)
    (globals : header.globals = compiled.indexed.base.globals.length) :
    CallableIndexedOwnedNestedCanonicalState.Packet owner header _ receipt.reached :=
  CallableIndexedOwnedNamedCanonicalEntries.packet functions owner header receipt.body receipt.reached
    prefixZero globals receipt.allowed

/-- Only the principal proof is added to the unchanged reached State. -/
def Receipt.nested (prefixZero : owner.key.capturePrefix = 0)
    (globals : header.globals = compiled.indexed.base.globals.length) :=
  CallableIndexedOwnedNamedCanonicalEntries.wrap functions owner header receipt.body receipt.reached
    prefixZero globals receipt.allowed

theorem Receipt.nested_pool (prefixZero : owner.key.capturePrefix = 0)
    (globals : header.globals = compiled.indexed.base.globals.length) :
    (receipt.nested prefixZero globals).val = receipt.reached := rfl

/-- Deep Source typing and the actual installed rows establish readiness. -/
theorem Receipt.nested_admission (wellFormed : ProgramWellFormed program)
    (prefixZero : owner.key.capturePrefix = 0)
    (globals : header.globals = compiled.indexed.base.globals.length) :
    Admission (CallableIndexedOwnedIndirectCallerProtocol.forget_slots
      (CallableIndexedOwnedNestedCallerProtocol.carrier (headers := headers) owner header))
      header.context (receipt.nested prefixZero globals) :=
  ⟨(receipt.source wellFormed).heapTyped, receipt.rows⟩

end Observations

private def poolBridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
    (fun _ => True) (protocol headers keys) :=
  CallableIndexedOwnedIndirectCallerProtocol.of_legacy CallableIndexedOwnedCallerProtocol.base

section Results
variable {functions owner}
  {faults : FunctionCalls.FaultRep}
  {initial : ProtectedStateTransition.Index} {argumentsPool : State headers keys initial}
  {header : CallableIndexedOwnedFunctionValues.Header compiled program} {arguments : List Dynamic.Value}
  (receipt : Receipt (registry := registry) functions owner argumentsPool header arguments)

/-- The result names the actual Header and BodyState directly and keeps the
full exit, reached pool and successful Source admission. -/
def ResultAt (outcome : Dynamic.ExpressionOutcome) (after : Dynamic.Heap)
    (value : Value) (finalStore : Store) (finalMap : LocationMap) (finalWorld : StoreTyping) : Prop :=
  Evaluates receipt.body.actualBody receipt.body.store (header.body.rename receipt.body.embedding) value finalStore ∧
  FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
    finalMap finalWorld header.function.resultType header.output faults outcome value ∧
  CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
  LocationMap.Extends receipt.body.mapping finalMap ∧ WorldExtends receipt.body.world finalWorld ∧
  AdministrativePreserved receipt.body.mapping receipt.body.store finalMap finalStore ∧
  Dynamic.HeapMetadataExtend receipt.body.heap after ∧
  TypedMixedNamedBody.ReachedExit compiled.compatible.checked (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions
    finalMap finalWorld (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: receipt.administrative)
    program header.function header.context (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
    receipt.body.environment receipt.body.heap after outcome ∧
  ∃ reached : State headers keys ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)),
    finalMap, finalWorld, after, finalStore, receipt.body.canonical⟩,
    Relates receipt.reached reached ∧
    PostAdmission (poolBridge (headers := headers) (keys := keys)) header.context header.function.resultType outcome reached

/-- The strict Source child is pointwise at this whole actual parameter input. -/
def PreservesAt (size : Nat) : Prop :=
  ∀ {outcome after},
    RecursiveNamedCallBounds.BodyTrace program size header.function header.context
      receipt.body.environment receipt.body.heap outcome after →
    ∃ value finalStore finalMap finalWorld,
      ResultAt receipt (faults := faults) outcome after value finalStore finalMap finalWorld

/-- Reflection returns an independent Source grade at the same native input. -/
def ReflectsAt (size : Nat) : Prop :=
  ∀ {value finalStore},
    EvaluationSize size receipt.body.actualBody receipt.body.store (header.body.rename receipt.body.embedding) value finalStore →
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.BodyTrace program sourceSize header.function header.context
        receipt.body.environment receipt.body.heap outcome after ∧
      ResultAt receipt (faults := faults) outcome after value finalStore finalMap finalWorld

/-- Forget only the retained exit and admission when entering the unchanged
low invocation result schema. -/
theorem PreservesAt.to_body {size : Nat} (meaning : PreservesAt receipt (faults := faults) size) :
    CallableIndexedOwnedInvocationBounds.SourceBodyAt (faults := faults) receipt.body receipt.reached size := by
  intro outcome after trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, heaps, maps, worlds,
    frame, metadata, _exit, reached, related, _post⟩ := meaning trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, heaps, maps, worlds,
    frame, metadata, reached, related⟩

theorem ReflectsAt.to_body {size : Nat} (meaning : ReflectsAt receipt (faults := faults) size) :
    CallableIndexedOwnedInvocationBounds.NativeBodyAt (faults := faults) receipt.body receipt.reached size := by
  intro value finalStore completed
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, _evaluated, represented, heaps, maps, worlds,
    frame, metadata, _exit, reached, related, _post⟩ := meaning completed
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, heaps, maps, worlds,
    frame, metadata, reached, related⟩

end Results

section BodyCallbacks
variable {functions owner}
  {faults : FunctionCalls.FaultRep}

/-- Parameter code and body continuation remain those of the original entry. -/
def SourceBodiesFor (header : CallableIndexedOwnedFunctionValues.Header compiled program) (budget : Nat) : Prop :=
  ∀ {initial : ProtectedStateTransition.Index} {argumentsPool : State headers keys initial} {arguments : List Dynamic.Value},
  ∀ receipt : Receipt (registry := registry) functions owner argumentsPool header arguments,
    ContinuationAgreement receipt.actual
      (initial.store.set receipt.frameLocation (encode compiled.indexed.ancestry.layout.frame (.state receipt.index)))
      (header.parameterCode.rename receipt.embedding) receipt.body.actualBody receipt.body.store
      (header.body.rename receipt.body.embedding) →
    RecursiveNamedBoundedContracts.Below budget (PreservesAt receipt (faults := faults))

/-- The measured prefix and saved caller restoration accompany the same
parameter input before a strict native body child is requested. -/
def NativeBodiesFor (header : CallableIndexedOwnedFunctionValues.Header compiled program) (budget : Nat) : Prop :=
  ∀ {initial : ProtectedStateTransition.Index} {argumentsPool : State headers keys initial} {arguments : List Dynamic.Value},
  ∀ receipt : Receipt (registry := registry) functions owner argumentsPool header arguments,
  ∀ {prefixSize bodyStore value finalStore},
    EvaluationSize prefixSize receipt.actual
      (initial.store.set receipt.frameLocation (encode compiled.indexed.ancestry.layout.frame (.state receipt.index)))
      (header.parameterCode.rename receipt.embedding) value bodyStore → prefixSize < budget →
    finalStore = bodyStore.set receipt.frameLocation
      (encode compiled.indexed.ancestry.layout.frame (argumentsPool.rows owner.position).authority.current) →
    RecursiveNamedBoundedContracts.Below budget (ReflectsAt receipt (faults := faults))

end BodyCallbacks

section Invocations
variable {functions owner}
  {header : CallableIndexedOwnedFunctionValues.Header compiled program}
  {source : TypedSource} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {scope : SourceCoreLocalCell.Scope} {ids : List ExpressionId}
  {faults : FunctionCalls.FaultRep}
  {callerPrefix : Nat} {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
    (fun index => CallableIndexedOwnedExpressionHeads.Globals (headers := headers) owner callerPrefix index.scope index.canonical) callerProtocol)
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {canonical : Environment} {environment : Dynamic.Environment}
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  (admitted : Admission (CallableIndexedOwnedIndirectCallerProtocol.forget_slots bridge) context initial)
  {originalTypes : List TypeSystem.Ty} {rawResult : TypeSystem.Ty} {predicates : List ProgramPredicate}
  (wellFormed : ProgramWellFormed program)
  (sourceRuntime : Dynamic.SourceRuntimeValid program context source)
  (covers : evidence.Covers context)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (argumentTypes : ExpressionsHaveTypes source context ids originalTypes)
  (application : SourceSemantics.DeclarationApplicationValid context header.instantiation originalTypes rawResult predicates)

include admitted wellFormed sourceRuntime covers locals argumentTypes application in
/-- Actual ordered Source arguments establish admission for the genuine
parameter input; only its strict body child is supplied. -/
theorem source_invocations (budget : Nat)
    (bodies : SourceBodiesFor (headers := headers) (functions := functions) (owner := owner) (registry := registry) (faults := faults) header budget) :
    CallableIndexedOwnedExpressionHeads.SourceInvocationsFor (source := source) (context := context)
      (evidence := evidence) (faults := faults) functions owner
      (CallableIndexedOwnedInvocationBounds.stableOwnerCondition (keys := keys) functions registry header) bridge initial
      (environment := environment) (ids := ids) budget := by
  intro sourceSize arguments middle middleMap middleWorld middleStore payloads evaluated argumentState
    _argumentRelated _maps _worlds frame _metadata _capture represented _heaps
    origin index metadata administrative actualContext actual ξ frameLocation physical selected history emitted
    entry agreement parameterPool parameterRelated _allowed child strict outcome after trace
  have arity : header.function.parameters.length = arguments.length :=
    (congrArg List.length header.parameters).trans ((List.length_map Prod.fst).trans represented.length.1)
  have sourceAdmission := CallableIndexedOwnedNamedArgumentAdmission.at_successful_arguments header wellFormed
    sourceRuntime covers locals admitted.heap argumentTypes application evaluated.sound arity
  have stable := StableRows.after_administrative (bridge.pool initial) (bridge.pool argumentState) admitted.rows frame
  let receipt : Receipt (registry := registry) functions owner (bridge.pool argumentState) header arguments :=
    { origin := origin, index := index, metadata := metadata, administrative := administrative,
      actualContext := actualContext, actual := actual, embedding := ξ, frameLocation := frameLocation,
      physical := physical, selected := selected, history := history, emitted := emitted,
      body := entry, reached := parameterPool, related := parameterRelated, stable := stable,
      heapTyped := sourceAdmission.1, argumentsTyped := sourceAdmission.2 }
  exact PreservesAt.to_body receipt (bodies receipt agreement child strict) trace

include admitted wellFormed sourceRuntime covers locals argumentTypes application in
/-- The native route uses the actual independently recovered Source argument
trace before selecting the same strict body input. -/
theorem native_invocations (budget : Nat)
    (bodies : NativeBodiesFor (headers := headers) (functions := functions) (owner := owner) (registry := registry) (faults := faults) header budget) :
    CallableIndexedOwnedExpressionHeads.NativeInvocationsFor (source := source) (context := context)
      (evidence := evidence) (faults := faults) functions owner
      (CallableIndexedOwnedInvocationBounds.stableOwnerCondition (keys := keys) functions registry header) bridge initial
      (environment := environment) (ids := ids) budget := by
  intro sourceSize arguments middle middleMap middleWorld middleStore payloads evaluated argumentState
    _argumentRelated _maps _worlds frame _metadata _capture represented _heaps
    origin index metadata administrative actualContext actual ξ frameLocation prefixSize bodyStore value finalStore
    physical selected history emitted prefixRun prefixWithin restored entry parameterPool parameterRelated _allowed child strict
    bodyValue bodyFinalStore completed
  have arity : header.function.parameters.length = arguments.length :=
    (congrArg List.length header.parameters).trans ((List.length_map Prod.fst).trans represented.length.1)
  have sourceAdmission := CallableIndexedOwnedNamedArgumentAdmission.at_successful_arguments header wellFormed
    sourceRuntime covers locals admitted.heap argumentTypes application evaluated.sound arity
  have stable := StableRows.after_administrative (bridge.pool initial) (bridge.pool argumentState) admitted.rows frame
  let receipt : Receipt (registry := registry) functions owner (bridge.pool argumentState) header arguments :=
    { origin := origin, index := index, metadata := metadata, administrative := administrative,
      actualContext := actualContext, actual := actual, embedding := ξ, frameLocation := frameLocation,
      physical := physical, selected := selected, history := history, emitted := emitted,
      body := entry, reached := parameterPool, related := parameterRelated, stable := stable,
      heapTyped := sourceAdmission.1, argumentsTyped := sourceAdmission.2 }
  exact ReflectsAt.to_body receipt (bodies receipt prefixRun prefixWithin restored child strict) completed

end Invocations
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedParameterReceipts
