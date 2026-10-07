import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedExpressionHeads
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNamedArgumentAdmission
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedSequenceProducer
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedBodyEntries
import Solcore.SourceSemantics.CoreLowering.CallableRuntimeBodyStaticOrigins
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNamedCanonicalEntries
import Solcore.SourceSemantics.CoreLowering.CallableRuntimeBodyEntryContracts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedBodyCanonicalEntries
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedBodyNestedEntries
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNestedCallerProtocol

/-! Named calls use Source admission at their real argument and parameter posts.
The complete static named profile stays independent of the actual body receipt.
Strict body callbacks consume only the genuine parameter entry. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedNamedExpressionHeads
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory SourceCoreCallableIndexedFrames
open RecursiveNamedCatalog RecursiveNamedCatalogInvocationBounds
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
open RecursiveNamedBoundedContracts
universe u
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (runtime : Bool)
  {certificates : CallableIndexedOwnedFunctionValues.Header compiled program → SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {expressionSyntax : CallableIndexedOwnedFunctionValues.Header compiled program → ExpressionId → Prop}
  {diagnosticPolicy : AssignmentDiagnosticPolicy}

/-- The real static profile retains the actual source body, code and compiler
parameter context; it carries no body execution promise. -/
abbrev Profile (header : CallableIndexedOwnedFunctionValues.Header compiled program)
    (administrative : Core.Context) :=
  MatchProfileWith (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (fun context => RecursiveNamedCatalogMutualMeaning.ContextFor runtime header.solved context header.function.evidence)
    (certificates header) diagnosticPolicy header (expressionSyntax header)
    (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) registry faults

private def poolBridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
    (fun _ => True) (protocol headers keys) :=
  CallableIndexedOwnedIndirectCallerProtocol.of_legacy CallableIndexedOwnedCallerProtocol.base

section ParameterEntries
variable {runtime owner functions}
  {header : CallableIndexedOwnedFunctionValues.Header compiled program}
  {scope : SourceCoreLocalCell.Scope} {canonical : Environment}
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  (argumentsPool : State headers keys ⟨scope, mapping, world, before, store, canonical⟩)
  {arguments : List Dynamic.Value} {origin : Word} {index : Int} {metadata : MetadataState}
  {administrative actualContext : Core.Context} {actual : Environment} {ξ : Renaming} {frameLocation : Location}

/-- The same genuine hook and actual Source binder allocation establish the
full typed body entry beside the exact reached parameter pool. -/
def parameter_entry
    (wellFormed : ProgramWellFormed program)
    (profile : Profile (registry := registry) (faults := faults) (certificates := certificates)
      (expressionSyntax := expressionSyntax) (diagnosticPolicy := diagnosticPolicy) runtime header administrative)
    (escaped : faults .controlEscapedFunction header.escaped)
    (physical : frameLocation = owner.key.frameLocation)
    (history : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
      (.state index) (.named origin) (some metadata))
    (entry : BodyState (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      headers owner.key.locations owner.key.capturePrefix functions registry header arguments before
      (store.set frameLocation (encode compiled.indexed.ancestry.layout.frame (.state index))) mapping world
      administrative actualContext actual ξ frameLocation (.state index) (.named origin))
    (parameterPool : State headers keys ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)),
      entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩)
    (stable : StableRows argumentsPool)
    (heapTyped : Dynamic.HeapWellTyped header.function.context before)
    (argumentsTyped : Dynamic.ValuesHaveTypes header.function.context before arguments header.types) :
    CallableIndexedOwnedAdmittedBodyEntries.Entry (poolBridge (headers := headers) (keys := keys))
      (condition := CallableIndexedOwnedAllocationProducer.StableOwner keys)
      (origin := CallableRuntimeBodyStaticOrigins.named (certificates := certificates header)
        (expressionSyntax := expressionSyntax header) (diagnosticPolicy := diagnosticPolicy) runtime profile escaped) (functions := functions) := by
  let original := CallableRuntimeBodyStaticOrigins.named_entry (protocol headers keys)
    (CallableIndexedOwnedAllocationProducer.StableOwner keys) runtime profile escaped entry parameterPool
    ⟨owner.position, .named origin, some metadata, physical.symm, history⟩
  have parameterFrame := Eq.mp (congrArg (fun location => AdministrativePreserved mapping
    (store.set location (encode compiled.indexed.ancestry.layout.frame (.state index))) entry.mapping entry.store) physical) entry.frame
  exact CallableIndexedOwnedAdmittedBodyEntries.Entry.of_parameters
    (poolBridge (headers := headers) (keys := keys)) original
    (CallableIndexedOwnedAdmittedBodyEntries.SourceReceipt.of_named wellFormed
      header.frame header.extended entry.allocation heapTyped argumentsTyped)
    argumentsPool stable owner.position history parameterFrame

end ParameterEntries


section BodySupport
variable {runtime owner functions}

/-- Static support is requested only at a genuine complete parameter entry. -/
def ProfilesFor (header : CallableIndexedOwnedFunctionValues.Header compiled program) :=
  ∀ {arguments before initialStore mapping world administrative actualContext actual ξ frameLocation current ghost},
    BodyState (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      headers owner.key.locations owner.key.capturePrefix functions registry header arguments before initialStore
      mapping world administrative actualContext actual ξ frameLocation current ghost →
    Profile (registry := registry) (faults := faults) (certificates := certificates)
      (expressionSyntax := expressionSyntax) (diagnosticPolicy := diagnosticPolicy) runtime header administrative

/-- Every field comes from the actual selected hook and parameter producer.
The complete BodyState retains its catalog, canonical layout, read and allocation effects;
Source admission describes the same argument and parameter heaps. -/
structure ParameterReceipt
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
  profile : Profile (registry := registry) (faults := faults) (certificates := certificates)
    (expressionSyntax := expressionSyntax) (diagnosticPolicy := diagnosticPolicy) runtime header administrative
  escaped : faults .controlEscapedFunction header.escaped

/-- The typed entry is computed from this receipt's exact BodyState and pool.
Its canonical and Source seed receipts stay available in the same packet. -/
def ParameterReceipt.admitted_entry
    {initial : ProtectedStateTransition.Index} {argumentsPool : State headers keys initial}
    {header : CallableIndexedOwnedFunctionValues.Header compiled program} {arguments : List Dynamic.Value}
    (receipt : ParameterReceipt (owner := owner) (functions := functions) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax) (diagnosticPolicy := diagnosticPolicy)
      (runtime := runtime) argumentsPool header arguments)
    (wellFormed : ProgramWellFormed program) :=
  parameter_entry argumentsPool wellFormed receipt.profile receipt.escaped receipt.physical receipt.history
    receipt.body receipt.reached receipt.stable receipt.heapTyped receipt.argumentsTyped

section ParameterObservations
variable {initial : ProtectedStateTransition.Index} {argumentsPool : State headers keys initial}
  {header : CallableIndexedOwnedFunctionValues.Header compiled program} {arguments : List Dynamic.Value}
  (receipt : ParameterReceipt (owner := owner) (functions := functions) (registry := registry) (faults := faults)
    (certificates := certificates) (expressionSyntax := expressionSyntax) (diagnosticPolicy := diagnosticPolicy)
    (runtime := runtime) argumentsPool header arguments)

/-- The actual catalog retains every original physical global slot at the
real body prefix, including any explicit captured prefix. -/
theorem ParameterReceipt.global_slots :
    CallableIndexedOwnedExpressionHeads.Globals (headers := headers) owner (owner.key.capturePrefix + 1)
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) receipt.body.canonical :=
  receipt.body.catalog.globals

/-- The original selected hook authenticates this exact named Source seed.
StableOwner alone is not used to infer that seed. -/
theorem ParameterReceipt.named_allowed :
    CallableIndexedOwnedNamedCanonicalEntries.condition functions owner header receipt.body :=
  CallableIndexedOwnedNamedCanonicalEntries.authorized functions owner header
    receipt.physical receipt.selected receipt.history receipt.emitted receipt.body

/-- With honest zero-prefix/global-count receipts, the actual parameter state
has the complete packet needed by nested formation and selected calls. -/
theorem ParameterReceipt.packet (prefixZero : owner.key.capturePrefix = 0)
    (globals : header.globals = compiled.indexed.base.globals.length) :
    CallableIndexedOwnedNestedCanonicalState.Packet owner header _ receipt.reached :=
  CallableIndexedOwnedNamedCanonicalEntries.packet functions owner header receipt.body receipt.reached
    prefixZero globals receipt.named_allowed

/-- Canonical slots accompany the same typed parameter entry. The Source
receipt and every stable row still describe its original actual pool. -/
def ParameterReceipt.canonical_entry (wellFormed : ProgramWellFormed program) :
    CallableIndexedOwnedAdmittedBodyEntries.Entry
      (CallableIndexedOwnedIndirectCallerProtocol.of_legacy
        (CallableIndexedOwnedCallerProtocol.canonical (headers := headers) owner (owner.key.capturePrefix + 1)))
      (condition := CallableIndexedOwnedAllocationProducer.StableOwner keys)
      (origin := CallableRuntimeBodyStaticOrigins.named (certificates := certificates header)
        (expressionSyntax := expressionSyntax header) (diagnosticPolicy := diagnosticPolicy)
        runtime receipt.profile receipt.escaped) (functions := functions) := by
  let base := receipt.admitted_entry wellFormed
  exact ⟨CallableIndexedOwnedBodyCanonicalEntries.wrap functions owner (owner.key.capturePrefix + 1)
    base.original receipt.global_slots, base.source, base.rows⟩

/-- Honest prefix receipts wrap this exact typed parameter entry for nested
formation; no Source or pool field is reconstructed from projected typing. -/
def ParameterReceipt.nested_entry (wellFormed : ProgramWellFormed program)
    (prefixZero : owner.key.capturePrefix = 0)
    (globals : header.globals = compiled.indexed.base.globals.length) :
    CallableIndexedOwnedAdmittedBodyEntries.Entry
      (CallableIndexedOwnedIndirectCallerProtocol.forget_slots
        (CallableIndexedOwnedNestedCallerProtocol.carrier (headers := headers) owner header))
      (condition := CallableIndexedOwnedAllocationProducer.StableOwner keys)
      (origin := CallableRuntimeBodyStaticOrigins.named (certificates := certificates header)
        (expressionSyntax := expressionSyntax header) (diagnosticPolicy := diagnosticPolicy)
        runtime receipt.profile receipt.escaped) (functions := functions) := by
  let base := receipt.admitted_entry wellFormed
  exact ⟨CallableIndexedOwnedBodyNestedEntries.wrap functions owner header base.original
    (receipt.packet prefixZero globals), base.source, base.rows⟩

end ParameterObservations

/-- Strict Source children are requested only at the authentic parameter packet,
with its original continuation agreement and computed typed entry. -/
def SourceBodiesFor (wellFormed : ProgramWellFormed program)
    (header : CallableIndexedOwnedFunctionValues.Header compiled program) (budget : Nat) : Prop :=
  ∀ {initial : ProtectedStateTransition.Index} {argumentsPool : State headers keys initial} {arguments : List Dynamic.Value},
  ∀ receipt : ParameterReceipt (owner := owner) (functions := functions) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax) (diagnosticPolicy := diagnosticPolicy)
      (runtime := runtime) argumentsPool header arguments,
    ContinuationAgreement receipt.actual
      (initial.store.set receipt.frameLocation (encode compiled.indexed.ancestry.layout.frame (.state receipt.index)))
      (header.parameterCode.rename receipt.embedding) receipt.body.actualBody receipt.body.store
      (header.body.rename receipt.body.embedding) →
    RecursiveNamedBoundedContracts.Below budget (CallableRuntimeBodyEntryContracts.PreservesAt
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      functions program (receipt.admitted_entry wellFormed).original)

/-- Native children retain the authentic measured parameter prefix and saved
caller write. The strict body is pointwise at that packet's exact typed entry. -/
def NativeBodiesFor (wellFormed : ProgramWellFormed program)
    (header : CallableIndexedOwnedFunctionValues.Header compiled program) (budget : Nat) : Prop :=
  ∀ {initial : ProtectedStateTransition.Index} {argumentsPool : State headers keys initial} {arguments : List Dynamic.Value},
  ∀ receipt : ParameterReceipt (owner := owner) (functions := functions) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax) (diagnosticPolicy := diagnosticPolicy)
      (runtime := runtime) argumentsPool header arguments,
  ∀ {prefixSize bodyStore value finalStore},
    EvaluationSize prefixSize receipt.actual
      (initial.store.set receipt.frameLocation (encode compiled.indexed.ancestry.layout.frame (.state receipt.index)))
      (header.parameterCode.rename receipt.embedding) value bodyStore → prefixSize < budget →
    finalStore = bodyStore.set receipt.frameLocation
      (encode compiled.indexed.ancestry.layout.frame (argumentsPool.rows owner.position).authority.current) →
    RecursiveNamedBoundedContracts.Below budget (CallableRuntimeBodyEntryContracts.ReflectsAt
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      functions program (receipt.admitted_entry wellFormed).original)

end BodySupport

section InvocationAdapters
variable {runtime owner functions}
  {header : CallableIndexedOwnedFunctionValues.Header compiled program}
  {source : TypedSource} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {scope : SourceCoreLocalCell.Scope} {ids : List ExpressionId}
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
  (profiles : ProfilesFor (headers := headers) (owner := owner) (functions := functions)
    (registry := registry) (faults := faults) (certificates := certificates)
    (expressionSyntax := expressionSyntax) (diagnosticPolicy := diagnosticPolicy) (runtime := runtime) header)
  (escaped : faults .controlEscapedFunction header.escaped)

include admitted wellFormed sourceRuntime covers locals argumentTypes application profiles escaped in
/-- Real Source argument execution and the authentic hook construct admission
for the exact reached parameter pool before a strict Source body is consumed. -/
theorem source_invocations (budget : Nat)
    (bodies : SourceBodiesFor (headers := headers) (keys := keys) (owner := owner) (functions := functions)
      (registry := registry) (faults := faults) (certificates := certificates)
      (expressionSyntax := expressionSyntax) (diagnosticPolicy := diagnosticPolicy) (runtime := runtime) wellFormed header budget) :
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
  let receipt : ParameterReceipt (owner := owner) (functions := functions) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax) (diagnosticPolicy := diagnosticPolicy)
      (runtime := runtime) (bridge.pool argumentState) header arguments :=
    { origin := origin, index := index, metadata := metadata, administrative := administrative,
      actualContext := actualContext, actual := actual, embedding := ξ, frameLocation := frameLocation,
      physical := physical, selected := selected, history := history, emitted := emitted,
      body := entry, reached := parameterPool, related := parameterRelated, stable := stable,
      heapTyped := sourceAdmission.1, argumentsTyped := sourceAdmission.2,
      profile := profiles entry, escaped := escaped }
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluation, result, heaps, maps, worlds,
      admin, metadata, _exit, reached, related⟩ :=
    bodies receipt agreement child strict trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluation, result, heaps, maps, worlds,
    admin, metadata, reached, related⟩

include admitted wellFormed sourceRuntime covers locals argumentTypes application profiles escaped in
/-- Native arguments first recover their actual independently sized Source
trace; the same Source admission and parameter pool drive the strict body. -/
theorem native_invocations (budget : Nat)
    (bodies : NativeBodiesFor (headers := headers) (keys := keys) (owner := owner) (functions := functions)
      (registry := registry) (faults := faults) (certificates := certificates)
      (expressionSyntax := expressionSyntax) (diagnosticPolicy := diagnosticPolicy) (runtime := runtime) wellFormed header budget) :
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
  let receipt : ParameterReceipt (owner := owner) (functions := functions) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax) (diagnosticPolicy := diagnosticPolicy)
      (runtime := runtime) (bridge.pool argumentState) header arguments :=
    { origin := origin, index := index, metadata := metadata, administrative := administrative,
      actualContext := actualContext, actual := actual, embedding := ξ, frameLocation := frameLocation,
      physical := physical, selected := selected, history := history, emitted := emitted,
      body := entry, reached := parameterPool, related := parameterRelated, stable := stable,
      heapTyped := sourceAdmission.1, argumentsTyped := sourceAdmission.2,
      profile := profiles entry, escaped := escaped }
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, result, heaps, maps, worlds,
      admin, metadata, _exit, reached, related⟩ :=
    bodies receipt prefixRun prefixWithin restored child strict completed
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, result, heaps, maps, worlds,
    admin, metadata, reached, related⟩

end InvocationAdapters


section Heads
variable {runtime owner functions}
  {source : TypedSource} {context : SourceSemantics.Context} (evidence : Dynamic.EvidenceEnvironment)
  {certificate : GenericExpressionMeaning.Certificate} {compilation : SourceCoreFunctions.Context}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
    (fun index => CallableIndexedOwnedExpressionHeads.Globals (headers := headers) owner compilation.administrativePrefix index.scope index.canonical) callerProtocol)
  (wellFormed : ProgramWellFormed program)
  (sourceRuntime : Dynamic.SourceRuntimeValid program context source)
  (covers : evidence.Covers context)
  (unique : NodeOccurrencesUnique source)
  (idsUnique : RequirementIdsUnique context)
  (sameLayouts : ∀ header, header ∈ headers → header.layouts = compiled.indexed.layouts)
  (escaped : ∀ header, header ∈ headers → faults .controlEscapedFunction header.escaped)
  (profiles : ∀ header, header ∈ headers → ProfilesFor (headers := headers) (owner := owner) (functions := functions)
    (registry := registry) (faults := faults) (certificates := certificates)
    (expressionSyntax := expressionSyntax) (diagnosticPolicy := diagnosticPolicy) (runtime := runtime) header)
  (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup)

include wellFormed sourceRuntime covers unique idsUnique sameLayouts escaped profiles owners in
/-- Named ordinary/direct heads use the authentic Source argument row at their
actual input, then consume only a typed strict body at the real parameter post. -/
theorem preserves_at (budget size : Nat) (within : size ≤ budget)
    (children : RecursiveNamedBoundedContracts.Below budget
      (CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
        (CallableIndexedOwnedIndirectCallerProtocol.forget_slots bridge)
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        context evidence source certificate faults))
    (bodies : ∀ header, header ∈ headers → SourceBodiesFor (headers := headers) (keys := keys) (owner := owner) (functions := functions)
      (registry := registry) (faults := faults) (certificates := certificates)
      (expressionSyntax := expressionSyntax) (diagnosticPolicy := diagnosticPolicy) (runtime := runtime) wellFormed header budget) :
    CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      (CallableIndexedOwnedIndirectCallerProtocol.forget_slots bridge)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      context evidence source
      (RecursiveNamedCallEvidenceHeads.Head (prepared := compiled.indexed.ancestry)
        (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        headers compilation source context evidence certificate) faults size := by
  intro scope id lowered head root found sourceTyped mapping world administrative environment canonical actual actualContext
    before store ξ outcome after environments heaps locals agrees typed initial admitted trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
      maps, worlds, frame, metadata, reached, related⟩ :=
    CallableIndexedOwnedExpressionHeads.preserves_at_with_sequence functions owner sameLayouts
      (fun header => CallableIndexedOwnedInvocationBounds.stableOwnerCondition (keys := keys) functions registry header)
      (fun header _ => CallableIndexedOwnedInvocationBounds.stable_owner_authorized functions registry header owner)
      bridge budget size within idsUnique unique owners head found initial environments heaps locals agrees typed
      (fun header _member callee ids codes form sequence _nativeTypes _packedType => by
        obtain ⟨originalTypes, rawResult, predicates, argumentTypes, _application⟩ :=
          CallableIndexedOwnedNamedArgumentAdmission.direct_arguments unique found form sourceTyped
        exact CallableIndexedOwnedAdmittedSequenceProducer.preserves
          (CallableIndexedOwnedIndirectCallerProtocol.forget_slots bridge) initial admitted sequence unique argumentTypes
          environments heaps locals agrees typed budget children)
      (fun header member callee ids form => by
        obtain ⟨originalTypes, rawResult, predicates, argumentTypes, application⟩ :=
          CallableIndexedOwnedNamedArgumentAdmission.direct_arguments unique found form sourceTyped
        exact source_invocations (owner := owner) (functions := functions) (runtime := runtime)
          bridge initial admitted wellFormed sourceRuntime covers locals argumentTypes application
          (profiles header member) (escaped header member) budget (bodies header member)) trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
    maps, worlds, frame, metadata, reached, related,
    after_expression_sized initial reached admitted wellFormed sourceRuntime covers locals sourceTyped trace frame⟩

include wellFormed sourceRuntime covers unique sameLayouts escaped profiles in
/-- Native heads retain the original native grade. The genuine reflected Source
argument and parent grades establish admission at their actual reached states. -/
theorem reflects_at (budget size : Nat) (within : size ≤ budget)
    (children : RecursiveNamedBoundedContracts.Below budget
      (CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
        (CallableIndexedOwnedIndirectCallerProtocol.forget_slots bridge)
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        context evidence source certificate faults))
    (bodies : ∀ header, header ∈ headers → NativeBodiesFor (headers := headers) (keys := keys) (owner := owner) (functions := functions)
      (registry := registry) (faults := faults) (certificates := certificates)
      (expressionSyntax := expressionSyntax) (diagnosticPolicy := diagnosticPolicy) (runtime := runtime) wellFormed header budget) :
    CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      (CallableIndexedOwnedIndirectCallerProtocol.forget_slots bridge)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      context evidence source
      (RecursiveNamedCallEvidenceHeads.Head (prepared := compiled.indexed.ancestry)
        (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        headers compilation source context evidence certificate) faults size := by
  intro scope id lowered head root found sourceTyped mapping world administrative environment canonical actual actualContext
    before store ξ value finalStore environments heaps locals agrees typed initial admitted completed
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
      maps, worlds, frame, metadata, reached, related⟩ :=
    CallableIndexedOwnedExpressionHeads.reflects_at_with_sequence functions owner sameLayouts
      (fun header => CallableIndexedOwnedInvocationBounds.stableOwnerCondition (keys := keys) functions registry header)
      (fun header _ => CallableIndexedOwnedInvocationBounds.stable_owner_authorized functions registry header owner)
      bridge budget size within head found initial environments heaps locals agrees typed
      (fun header _member callee ids codes form sequence _nativeTypes _packedType => by
        obtain ⟨originalTypes, rawResult, predicates, argumentTypes, _application⟩ :=
          CallableIndexedOwnedNamedArgumentAdmission.direct_arguments unique found form sourceTyped
        exact CallableIndexedOwnedAdmittedSequenceProducer.reflects
          (CallableIndexedOwnedIndirectCallerProtocol.forget_slots bridge) initial admitted sequence unique argumentTypes
          environments heaps locals agrees typed budget children)
      (fun header member callee ids form => by
        obtain ⟨originalTypes, rawResult, predicates, argumentTypes, application⟩ :=
          CallableIndexedOwnedNamedArgumentAdmission.direct_arguments unique found form sourceTyped
        exact native_invocations (owner := owner) (functions := functions) (runtime := runtime)
          bridge initial admitted wellFormed sourceRuntime covers locals argumentTypes application
          (profiles header member) (escaped header member) budget (bodies header member)) completed
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
    maps, worlds, frame, metadata, reached, related,
    after_expression_sized initial reached admitted wellFormed sourceRuntime covers locals sourceTyped trace frame⟩

end Heads

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedNamedExpressionHeads
