import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicPreparedBodyBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedExpressionRuntimeBounds
import Solcore.SourceSemantics.CoreLowering.CallableRuntimeBodyMutualMeaning

/-! Actual public named parameter receipts close through the existing measured
family. Each child retains its own Header, Source input and administrative
context; the original expression support fold and finish proofs preserve the
same returned pool and independently sized Source reflection. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 6000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicPreparedNamedFamilyClosure
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedHistory SourceCoreCallableIndexedFrames
open CallableIndexedOwnedPreparedNamedParameterReceipts (Receipt)
open CallableIndexedOwnedPublicPreparedTokenReadyNamedExpressionBounds (PublicReceipt)
open CallableIndexedOwnedPublicPreparedSourceSites (Validity)
open RecursiveNamedCatalogInvocationBounds (BodyState)
open ProtectedStateTransition

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)

/-- The family index is the complete actual parameter input. -/
structure Index where
  header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)
  member : header ∈ headers
  initial : ProtectedStateTransition.Index
  argumentsPool : State headers keys initial
  arguments : List Dynamic.Value
  receipt : Receipt (registry := registry) functions owner argumentsPool header arguments

section Ordinary
variable {initial : ProtectedStateTransition.Index} {argumentsPool : State headers keys initial}
  {header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
  {arguments : List Dynamic.Value}
  (receipt : Receipt (registry := registry) functions owner argumentsPool header arguments)
  (prefixZero : owner.key.capturePrefix = 0)

private def ordinary_catalog : RecursiveNamedCatalog.Entry
    (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    headers owner.key.locations 0 1 (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
    receipt.body.mapping receipt.body.world receipt.body.heap receipt.body.store receipt.body.canonical where
  authority := {
    frameLocation := receipt.body.catalog.authority.frameLocation
    unmapped := receipt.body.catalog.authority.unmapped
    typed := receipt.body.catalog.authority.typed
    current := receipt.body.catalog.authority.current
    ghost := receipt.body.catalog.authority.ghost
    frame := receipt.body.catalog.authority.frame
    records := receipt.body.catalog.authority.records
    snapshots := receipt.body.catalog.authority.snapshots
    distinct := receipt.body.catalog.authority.distinct
    captures := by simpa only [prefixZero] using receipt.body.catalog.authority.captures }
  globals := by simpa only [prefixZero, Nat.zero_add] using receipt.body.catalog.globals

/-- Reindex only the catalog prefix. Every runtime field is copied literally
from the original actual BodyState. -/
def ordinary_entry : BodyState (prepared := compiled.indexed.ancestry)
    (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    headers owner.key.locations 0 functions registry header arguments initial.heap
    (initial.store.set receipt.frameLocation (encode compiled.indexed.ancestry.layout.frame (.state receipt.index)))
    initial.mapping initial.world receipt.administrative receipt.actualContext receipt.actual receipt.embedding
    receipt.frameLocation (.state receipt.index) (.named receipt.origin) :=
  BodyState.of_receipts receipt.body.environment receipt.body.heap receipt.body.canonical receipt.body.actualBody
    receipt.body.store receipt.body.mapping receipt.body.world receipt.body.embedding receipt.body.allocation
    receipt.body.environments receipt.body.heaps receipt.body.locals receipt.body.maps receipt.body.worlds
    receipt.body.frame receipt.body.metadata receipt.body.lookups receipt.body.actualTyped
    (ordinary_catalog functions owner receipt prefixZero) receipt.body.reference receipt.body.state
    receipt.body.catalog_frame receipt.body.catalog_current receipt.body.catalog_ghost

end Ordinary

/-- The principal packet and original pool accompany the actual selected
Header. The carrier projects only the unchanged base State. -/
def bridge (index : Index (headers := headers) (registry := registry) functions owner) :=
  CallableIndexedOwnedIndirectCallerProtocol.forget_slots
    (CallableIndexedOwnedNestedCallerProtocol.carrier (headers := headers) owner index.header)

variable {expressionSyntax : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) → ExpressionId → Prop}
  (publicReceipts : ∀ header, header ∈ headers → PublicReceipt header)
  {diagnostics : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial compiled.compatible.checked)}
  {table : SourceCoreFaultSites.Table}

/-- Genuine child compilation and the precise reached table interpretation
belong to this receipt's own administrative context. No body meaning is stored. -/
structure Inputs (index : Index (headers := headers) (registry := registry) functions owner) where
  children : CallableIndexedOwnedNamedTokenProfileExtraction.Children
    (header := index.header) (headers := headers) (expressionSyntax := expressionSyntax)
    CallableIndexedOwnedPublicReadyNamedExpressionBounds.compilation
    (SourceCoreCompatibleCatalog.packTypes (index.header.bindings.map Prod.snd) :: index.receipt.administrative)
  interpretations : ∀ extracted : CallableIndexedOwnedPublicCatalogPreparedReceipts.CatalogReceipt
      (headers := headers) (compilation := CallableIndexedOwnedPublicReadyNamedExpressionBounds.compilation)
      (expressionSyntax := expressionSyntax) (administrative := index.receipt.administrative)
      (publicReceipts index.header index.member),
    ∀ context, Validity index.header context →
      CallableIndexedOwnedPublicPreparedAssignmentReadiness.ReachedInterpretations
        (context := context)
        (certificates := CallableIndexedOwnedReadyNamedFamilyClosure.certificates (headers := headers)
          CallableIndexedOwnedPublicReadyNamedExpressionBounds.compilation index.header)
        (administrative := SourceCoreCompatibleCatalog.packTypes (index.header.bindings.map Prod.snd) :: index.receipt.administrative)
        (factory := AssignmentDiagnosticOrigins.Factory.prepared extracted.operandsTyped extracted.assignments)
        (faults := faults) (registry := registry) index.header (bridge functions owner index)
        (publicReceipts index.header index.member) functions table

variable (prefixZero : owner.key.capturePrefix = 0)
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (complete : RecursiveNamedCatalogNativeContexts.Complete (prepared := compiled.indexed.ancestry)
    (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers)
  (owners : ((Program.ofChecked compiled.sourceProgram).functions.map (fun definition => definition.body.owner)).Nodup)
  (diagnosticsFound : compiled.indexed.base.diagnostics = some diagnostics)
  (rebuilt : diagnostics.tableForRegistry registry extension = .ok table)
  (operandIncluded : ∀ header member reason token, GenericAssignmentDiagnostics.OperandRep
    (publicReceipts header member).original.prepared.compilation.own.assignments reason token → faults reason token)
  (unaryIncluded : ∀ header member reason token, EmittedDiagnosticTokenPlan.UnaryRep
    (publicReceipts header member).original.prepared.compilation.own.assignments reason token → faults reason token)
  (uninitialized : ∀ header ∈ headers, ∀ id location, faults (.uninitializedLocation location) (header.reasonAt id))
  (missing : ∀ header ∈ headers, ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((header.reasonAt id).add tag))
  (escaped : ∀ header, header ∈ headers → faults .controlEscapedFunction header.escaped)
  (inputs : ∀ index : Index (headers := headers) (registry := registry) functions owner,
    Inputs (table := table) (faults := faults) (expressionSyntax := expressionSyntax) functions owner publicReceipts index)

/-- Both meanings belong to the same actual parameter receipt. -/
def Family (index : Index (headers := headers) (registry := registry) functions owner) (size : Nat) : Prop :=
  CallableIndexedOwnedPreparedNamedParameterReceipts.PreservesAt index.receipt (faults := faults) size ∧
    CallableIndexedOwnedPreparedNamedParameterReceipts.ReflectsAt index.receipt (faults := faults) size

private def producer (index : Index (headers := headers) (registry := registry) functions owner) :
    MarkedAllocation.Producer (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner index.header)
      index.header.layouts compiled.indexed.ancestry.layout.frame
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) :=
  (publicReceipts index.header index.member).original.aligned.layouts.symm ▸
    CallableIndexedOwnedNestedCanonicalState.markedProducer owner index.header
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)

private theorem ready_layout {first second : SourceCoreAllocationLayouts.Prepared}
    {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment}
    {model : GenericHeap.PayloadModel catalog projects definitions}
    (index : Index (headers := headers) (registry := registry) functions owner) (same : first = second)
    (marked : MarkedAllocation.Producer (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner index.header)
      second compiled.indexed.ancestry.layout.frame model)
    {location : Location} {native : NativeFrame}
    (ready : OrdinaryAllocation.ReadyAt marked.toOrdinary location native) :
    OrdinaryAllocation.ReadyAt ((same.symm ▸ marked).toOrdinary) location native := by
  cases same
  exact ready

private theorem acquire (index : Index (headers := headers) (registry := registry) functions owner)
    (location : Location) (native : NativeFrame)
    (stable : CallableIndexedOwnedAllocationProducer.StableOwner keys location native) :
    OrdinaryAllocation.ReadyAt (producer functions owner publicReceipts index).toOrdinary location native :=
  ready_layout functions owner index (publicReceipts index.header index.member).original.aligned.layouts
    (CallableIndexedOwnedNestedCanonicalState.markedProducer owner index.header
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions))
    (CallableIndexedOwnedNestedCanonicalState.readyAt_of_stableOwner owner index.header
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) stable)

include prefixZero extension faithful observations functionTypes wellFormed complete owners diagnosticsFound rebuilt
  operandIncluded unaryIncluded uninitialized missing escaped inputs in
/-- Strict actual callee receipts close the original expression fold. The
chosen public flow and existing finish then return this same parameter pool. -/
private theorem preserves_step (budget : Nat)
    (below : ∀ index : Index (headers := headers) (registry := registry) functions owner,
      RecursiveNamedBoundedContracts.Below budget (Family (faults := faults) functions owner index))
    (index : Index (headers := headers) (registry := registry) functions owner) :
    CallableIndexedOwnedPreparedNamedParameterReceipts.PreservesAt index.receipt (faults := faults) budget := by
  intro outcome after trace
  have bodies : ∀ header, header ∈ headers →
      CallableIndexedOwnedPreparedNamedParameterReceipts.SourceBodiesFor
        (headers := headers) (functions := functions) (owner := owner) (registry := registry) (faults := faults) header budget := by
    intro header member initial argumentsPool arguments receipt _agreement size strict
    exact (below ⟨header, member, initial, argumentsPool, arguments, receipt⟩ size strict).1
  have meaning : ∀ context, Validity index.header context → RecursiveNamedHeaderContracts.AtMost budget
      (fun child => CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt (bridge functions owner index)
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        context index.header.function.evidence index.header.function.source
        (CallableIndexedOwnedReadyNamedFamilyClosure.certificates (headers := headers)
          CallableIndexedOwnedPublicReadyNamedExpressionBounds.compilation index.header context) faults child) := by
    intro context valid child within
    exact CallableIndexedOwnedPreparedNamedExpressionRuntimeBounds.preserves_at_runtime
      (compilation := CallableIndexedOwnedPublicReadyNamedExpressionBounds.compilation index.header)
      (fuel := index.header.readFuel) (solved := index.header.solved) (reasonAt := index.header.reasonAt)
      functions extension faithful observations functionTypes owner
      (CallableIndexedOwnedNestedCallerProtocol.carrier (headers := headers) owner index.header)
      (CallableIndexedOwnedNestedCanonicalState.administrativeTransport (headers := headers) owner index.header)
      index.header.function.evidence wellFormed valid.2 valid.1.covers index.header.unique owners valid.1.runtime.1
      (fun header member => (publicReceipts header member).original.aligned.layouts)
      (uninitialized index.header index.member) (missing index.header index.member)
      valid.1.ledger valid.1.runtime budget child within bodies
  obtain ⟨value, finalStore, evaluated, finalMap, finalWorld, represented, heaps, maps, worlds,
      frame, metadata, exit, reached, related, post⟩ :=
    CallableIndexedOwnedPublicPreparedBodyBounds.preserves_at_entry
      (header := index.header) (bridge := bridge functions owner index)
      (issued := publicReceipts index.header index.member) (functions := functions)
      (extension := extension) (faithful := faithful) (observations := observations)
      (condition := CallableIndexedOwnedAllocationProducer.StableOwner keys)
      (producer := producer functions owner publicReceipts index)
      (acquire := acquire functions owner publicReceipts index)
      (transport := CallableIndexedOwnedNestedCanonicalState.administrativeTransport (headers := headers) owner index.header)
      (bindings := CallableIndexedOwnedNestedCanonicalState.bindings (headers := headers) owner index.header)
      (wellFormed := wellFormed) (diagnosticsFound := diagnosticsFound) (rebuilt := rebuilt)
      (operandIncluded := operandIncluded index.header index.member)
      (unaryIncluded := unaryIncluded index.header index.member) (owner := owner) (complete := complete)
      (entry := ordinary_entry functions owner index.receipt prefixZero)
      (sourceReceipt := index.receipt.source wellFormed) (children := (inputs index).children)
      (initial := index.receipt.nested prefixZero (publicReceipts index.header index.member).original.aligned.globals)
      (stable := index.receipt.rows) (gate := index.receipt.stable_owner)
      (escapedFault := escaped index.header index.member) (interpretations := (inputs index).interpretations)
      budget budget (Nat.le_refl budget) meaning trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, heaps, maps, worlds,
    frame, metadata, exit, reached.val, related, ⟨post.rows, post.successful⟩⟩

include prefixZero extension faithful observations functionTypes wellFormed complete diagnosticsFound rebuilt
  operandIncluded unaryIncluded uninitialized missing escaped inputs in
/-- Reflection recovers an independent Source grade at the same actual
parameter input, keeping its full reached exit and returned pool. -/
private theorem reflects_step (budget : Nat)
    (below : ∀ index : Index (headers := headers) (registry := registry) functions owner,
      RecursiveNamedBoundedContracts.Below budget (Family (faults := faults) functions owner index))
    (index : Index (headers := headers) (registry := registry) functions owner) :
    CallableIndexedOwnedPreparedNamedParameterReceipts.ReflectsAt index.receipt (faults := faults) budget := by
  intro value finalStore completed
  have bodies : ∀ header, header ∈ headers →
      CallableIndexedOwnedPreparedNamedParameterReceipts.NativeBodiesFor
        (headers := headers) (functions := functions) (owner := owner) (registry := registry) (faults := faults) header budget := by
    intro header member initial argumentsPool arguments receipt prefixSize bodyStore value finalStore
      _prefixRun _prefixWithin _restored size strict
    exact (below ⟨header, member, initial, argumentsPool, arguments, receipt⟩ size strict).2
  have meaning : ∀ context, Validity index.header context → RecursiveNamedBoundedContracts.Below budget
      (fun child => CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt (bridge functions owner index)
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        context index.header.function.evidence index.header.function.source
        (CallableIndexedOwnedReadyNamedFamilyClosure.certificates (headers := headers)
          CallableIndexedOwnedPublicReadyNamedExpressionBounds.compilation index.header context) faults child) := by
    intro context valid child strict
    exact CallableIndexedOwnedPreparedNamedExpressionRuntimeBounds.reflects_at_runtime
      (compilation := CallableIndexedOwnedPublicReadyNamedExpressionBounds.compilation index.header)
      (fuel := index.header.readFuel) (solved := index.header.solved) (reasonAt := index.header.reasonAt)
      functions extension faithful observations functionTypes owner
      (CallableIndexedOwnedNestedCallerProtocol.carrier (headers := headers) owner index.header)
      (CallableIndexedOwnedNestedCanonicalState.administrativeTransport (headers := headers) owner index.header)
      index.header.function.evidence wellFormed valid.2 valid.1.covers index.header.unique
      (fun header member => (publicReceipts header member).original.aligned.layouts)
      (uninitialized index.header index.member) (missing index.header index.member)
      valid.1.ledger valid.1.runtime budget child (Nat.le_of_lt strict) bodies
  obtain ⟨sourceSize, outcome, after, trace, finalMap, finalWorld, represented, heaps, maps, worlds,
      frame, metadata, exit, reached, related, post⟩ :=
    CallableIndexedOwnedPublicPreparedBodyBounds.reflects_at_entry
      (header := index.header) (bridge := bridge functions owner index)
      (issued := publicReceipts index.header index.member) (functions := functions)
      (extension := extension) (faithful := faithful) (observations := observations)
      (condition := CallableIndexedOwnedAllocationProducer.StableOwner keys)
      (producer := producer functions owner publicReceipts index)
      (acquire := acquire functions owner publicReceipts index)
      (transport := CallableIndexedOwnedNestedCanonicalState.administrativeTransport (headers := headers) owner index.header)
      (bindings := CallableIndexedOwnedNestedCanonicalState.bindings (headers := headers) owner index.header)
      (wellFormed := wellFormed) (diagnosticsFound := diagnosticsFound) (rebuilt := rebuilt)
      (operandIncluded := operandIncluded index.header index.member)
      (unaryIncluded := unaryIncluded index.header index.member) (owner := owner) (complete := complete)
      (entry := ordinary_entry functions owner index.receipt prefixZero)
      (sourceReceipt := index.receipt.source wellFormed) (children := (inputs index).children)
      (initial := index.receipt.nested prefixZero (publicReceipts index.header index.member).original.aligned.globals)
      (stable := index.receipt.rows) (gate := index.receipt.stable_owner)
      (escapedFault := escaped index.header index.member) (interpretations := (inputs index).interpretations)
      budget budget (Nat.le_refl budget) functionTypes meaning completed
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, completed.sound, represented, heaps, maps, worlds,
    frame, metadata, exit, reached.val, related, ⟨post.rows, post.successful⟩⟩


include prefixZero extension faithful observations functionTypes wellFormed complete owners diagnosticsFound rebuilt
  operandIncluded unaryIncluded uninitialized missing escaped inputs in
/-- The existing measured closer closes both meanings of every actual public
parameter receipt. No completed body or expression law is an input. -/
theorem closed_at (size : Nat) :
    ∀ index : Index (headers := headers) (registry := registry) functions owner,
      Family (faults := faults) functions owner index size := by
  apply CallableRuntimeBodyMutualMeaning.close_family (Family (faults := faults) functions owner)
  intro budget below index
  constructor
  · exact preserves_step (functions := functions) (owner := owner) (publicReceipts := publicReceipts)
      (prefixZero := prefixZero) (extension := extension) (faithful := faithful) (observations := observations)
      (functionTypes := functionTypes) (wellFormed := wellFormed) (complete := complete) (owners := owners)
      (diagnosticsFound := diagnosticsFound) (rebuilt := rebuilt) (operandIncluded := operandIncluded)
      (unaryIncluded := unaryIncluded) (uninitialized := uninitialized) (missing := missing)
      (escaped := escaped) (inputs := inputs) budget below index
  · exact reflects_step (functions := functions) (owner := owner) (publicReceipts := publicReceipts)
      (prefixZero := prefixZero) (extension := extension) (faithful := faithful) (observations := observations)
      (functionTypes := functionTypes) (wellFormed := wellFormed) (complete := complete)
      (diagnosticsFound := diagnosticsFound) (rebuilt := rebuilt) (operandIncluded := operandIncluded)
      (unaryIncluded := unaryIncluded) (uninitialized := uninitialized) (missing := missing)
      (escaped := escaped) (inputs := inputs) budget below index

include prefixZero extension faithful observations functionTypes wellFormed complete owners diagnosticsFound rebuilt
  operandIncluded unaryIncluded uninitialized missing escaped inputs in
/-- The actual Source continuation consumes only the corresponding closed
strict child; original parameter continuation agreement stays unchanged. -/
theorem source_bodies (header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))
    (member : header ∈ headers) (budget : Nat) :
    CallableIndexedOwnedPreparedNamedParameterReceipts.SourceBodiesFor
      (headers := headers) (functions := functions) (owner := owner) (registry := registry) (faults := faults) header budget := by
  intro initial argumentsPool arguments receipt _agreement size _strict
  exact (closed_at (functions := functions) (owner := owner) (publicReceipts := publicReceipts)
      (prefixZero := prefixZero) (extension := extension) (faithful := faithful) (observations := observations)
      (functionTypes := functionTypes) (wellFormed := wellFormed) (complete := complete) (owners := owners)
      (diagnosticsFound := diagnosticsFound) (rebuilt := rebuilt) (operandIncluded := operandIncluded)
      (unaryIncluded := unaryIncluded) (uninitialized := uninitialized) (missing := missing)
      (escaped := escaped) (inputs := inputs) size
    ⟨header, member, initial, argumentsPool, arguments, receipt⟩).1

include prefixZero extension faithful observations functionTypes wellFormed complete owners diagnosticsFound rebuilt
  operandIncluded unaryIncluded uninitialized missing escaped inputs in
/-- The actual measured native prefix and saved caller restoration stay
original. Reflection returns the independent Source grade at this receipt. -/
theorem native_bodies (header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))
    (member : header ∈ headers) (budget : Nat) :
    CallableIndexedOwnedPreparedNamedParameterReceipts.NativeBodiesFor
      (headers := headers) (functions := functions) (owner := owner) (registry := registry) (faults := faults) header budget := by
  intro initial argumentsPool arguments receipt prefixSize bodyStore value finalStore
    _prefixRun _prefixWithin _restored size _strict
  exact (closed_at (functions := functions) (owner := owner) (publicReceipts := publicReceipts)
      (prefixZero := prefixZero) (extension := extension) (faithful := faithful) (observations := observations)
      (functionTypes := functionTypes) (wellFormed := wellFormed) (complete := complete) (owners := owners)
      (diagnosticsFound := diagnosticsFound) (rebuilt := rebuilt) (operandIncluded := operandIncluded)
      (unaryIncluded := unaryIncluded) (uninitialized := uninitialized) (missing := missing)
      (escaped := escaped) (inputs := inputs) size
    ⟨header, member, initial, argumentsPool, arguments, receipt⟩).2

section Expressions
universe u
variable {callerCompilation : SourceCoreFunctions.Context}
  {callerProtocol : Protocol.{u, 0} (Records keys)}
  (caller : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
    (fun index => CallableIndexedOwnedExpressionHeads.Globals (headers := headers)
      owner callerCompilation.administrativePrefix index.scope index.canonical) callerProtocol)
  (transport : AdministrativeTransport callerProtocol)
  {source : TypedSource} {context : SourceSemantics.Context} (evidence : Dynamic.EvidenceEnvironment)
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word} {fuel : Nat}
  (sourceRuntime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context source)
  (covers : evidence.Covers context) (unique : NodeOccurrencesUnique source)
  (idsUnique : RequirementIdsUnique context)
  (callerUninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (callerMissing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))

include prefixZero extension faithful observations functionTypes wellFormed complete owners diagnosticsFound rebuilt
  operandIncluded unaryIncluded uninitialized missing escaped inputs transport sourceRuntime covers unique idsUnique callerUninitialized callerMissing in
/-- Ordinary and direct named calls close internally at authentic actual
parameter receipts, while the original runtime expression fold keeps the
caller's complete packet and actual post. -/
theorem preserves_at_runtime (sameLedger : context.solvedRequirements = solved)
    (runtimeLedger : RuntimeRequirementLedgerValid context) (budget size : Nat) (within : size ≤ budget) :
    CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      (CallableIndexedOwnedIndirectCallerProtocol.forget_slots caller)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) context evidence source
      (CallableIndexedOwnedPreparedNamedExpressionRuntimeBounds.RuntimeTree (headers := headers)
        (compilation := callerCompilation) (source := source) (context := context)
        (solved := solved) (reasonAt := reasonAt) (fuel := fuel) evidence) faults size :=
  CallableIndexedOwnedPreparedNamedExpressionRuntimeBounds.preserves_at_runtime
    functions extension faithful observations functionTypes owner caller transport evidence
    wellFormed sourceRuntime covers unique owners idsUnique
    (fun header member => (publicReceipts header member).original.aligned.layouts)
    callerUninitialized callerMissing sameLedger runtimeLedger budget size within
    (fun header member => source_bodies (functions := functions) (owner := owner) (publicReceipts := publicReceipts)
      (prefixZero := prefixZero) (extension := extension) (faithful := faithful) (observations := observations)
      (functionTypes := functionTypes) (wellFormed := wellFormed) (complete := complete) (owners := owners)
      (diagnosticsFound := diagnosticsFound) (rebuilt := rebuilt) (operandIncluded := operandIncluded)
      (unaryIncluded := unaryIncluded) (uninitialized := uninitialized) (missing := missing)
      (escaped := escaped) (inputs := inputs) header member budget)

include prefixZero extension faithful observations functionTypes wellFormed complete owners diagnosticsFound rebuilt
  operandIncluded unaryIncluded uninitialized missing escaped inputs transport sourceRuntime covers unique callerUninitialized callerMissing in
/-- Native reflection retains the same caller pool and recovers a separate
Source grade using the closed actual parameter family. -/
theorem reflects_at_runtime (sameLedger : context.solvedRequirements = solved)
    (runtimeLedger : RuntimeRequirementLedgerValid context) (budget size : Nat) (within : size ≤ budget) :
    CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      (CallableIndexedOwnedIndirectCallerProtocol.forget_slots caller)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) context evidence source
      (CallableIndexedOwnedPreparedNamedExpressionRuntimeBounds.RuntimeTree (headers := headers)
        (compilation := callerCompilation) (source := source) (context := context)
        (solved := solved) (reasonAt := reasonAt) (fuel := fuel) evidence) faults size :=
  CallableIndexedOwnedPreparedNamedExpressionRuntimeBounds.reflects_at_runtime
    functions extension faithful observations functionTypes owner caller transport evidence
    wellFormed sourceRuntime covers unique
    (fun header member => (publicReceipts header member).original.aligned.layouts)
    callerUninitialized callerMissing sameLedger runtimeLedger budget size within
    (fun header member => native_bodies (functions := functions) (owner := owner) (publicReceipts := publicReceipts)
      (prefixZero := prefixZero) (extension := extension) (faithful := faithful) (observations := observations)
      (functionTypes := functionTypes) (wellFormed := wellFormed) (complete := complete) (owners := owners)
      (diagnosticsFound := diagnosticsFound) (rebuilt := rebuilt) (operandIncluded := operandIncluded)
      (unaryIncluded := unaryIncluded) (uninitialized := uninitialized) (missing := missing)
      (escaped := escaped) (inputs := inputs) header member budget)

end Expressions

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicPreparedNamedFamilyClosure
