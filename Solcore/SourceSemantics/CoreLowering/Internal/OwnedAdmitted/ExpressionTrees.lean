import Solcore.SourceSemantics.CoreLowering.Internal.Owned.ExpressionHeads
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.NestedEntries
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedAdmitted.LexicalBodies
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.RuntimeIndirectCalls
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.RuntimeBodies
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.CanonicalCallerState
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedAdmitted.StagedExpressions

/-!
# Admitted profile: expression trees

Named expression heads, closed named bodies, and tree and sequence bounds.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedNamedExpressionHeads
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedClosedNamedBodies
/-! Closed named callees have authentic static profiles with no expression
leaves. This bounded grammar supports the original nil, absent-let, block and
return-unit forms accepted by that profile. It supplies no mixed-body closure.
The existing singleton mutual proof consumes each real parameter receipt and
returns its exact reached pool and Source exit; no execution law is an input. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedClosedNamedBodies
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedOwnedFunctionState ProtectedStateTransition

/-- The closed callee profile has no executable expression leaves. -/
def noExpressions (_ : SourceSemantics.Context) : GenericExpressionMeaning.Certificate :=
  fun _ _ _ => False

def noExpressionSyntax (_ : ExpressionId) : Prop := False

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)

/-- All authentic hook, Source, allocation and static profile fields are kept. -/
abbrev Receipt {index : Index} (argumentsPool : State headers keys index)
    (header : CallableIndexedOwnedFunctionValues.Header compiled program) (arguments : List Dynamic.Value) :=
  CallableIndexedOwnedAdmittedNamedExpressionHeads.ParameterReceipt
    (owner := owner) (functions := functions) (registry := registry) (faults := faults)
    (certificates := fun _ => noExpressions) (expressionSyntax := fun _ => noExpressionSyntax)
    (diagnosticPolicy := .reachable) (runtime := true) argumentsPool header arguments

variable {index : Index} {argumentsPool : State headers keys index}
  {header : CallableIndexedOwnedFunctionValues.Header compiled program} {arguments : List Dynamic.Value}
  (receipt : Receipt (registry := registry) (faults := faults) functions owner argumentsPool header arguments)
  (wellFormed : ProgramWellFormed program)
  (sameLayout : header.layouts = compiled.indexed.layouts)
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)

private def marked : MarkedAllocation.Producer (protocol headers keys)
    header.layouts compiled.indexed.ancestry.layout.frame
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) :=
  sameLayout.symm ▸ CallableIndexedOwnedMarkedAllocation.producer headers keys
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)

private theorem ready_layout {first second : SourceCoreAllocationLayouts.Prepared}
    (same : first = second)
    (producer : MarkedAllocation.Producer (protocol headers keys)
      second compiled.indexed.ancestry.layout.frame
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions))
    {location : Location} {native : NativeFrame}
    (ready : OrdinaryAllocation.ReadyAt producer.toOrdinary location native) :
    OrdinaryAllocation.ReadyAt ((same.symm ▸ producer).toOrdinary) location native := by
  cases same
  exact ready

private theorem acquire (location : Location) (native : NativeFrame)
    (stable : CallableIndexedOwnedAllocationProducer.StableOwner keys location native) :
    OrdinaryAllocation.ReadyAt (marked (headers := headers) (keys := keys) (registry := registry) functions sameLayout).toOrdinary location native :=
  ready_layout (headers := headers) (keys := keys) (registry := registry) functions sameLayout
    (CallableIndexedOwnedMarkedAllocation.producer headers keys
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions))
    (CallableIndexedOwnedAllocationProducer.readyAt_of_stableOwner (headers := headers)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) stable)

include wellFormed sameLayout extension faithful observations in
/-- The existing measured closer proves the exact computed entry, including
ReachedExit. Only impossible static expression leaves are discharged. -/
theorem parameter_preserves [FunctionCalls.FaultTokens faults] (size : Nat) :
    CallableRuntimeBodyEntryContracts.PreservesAt (registry := registry) (faults := faults)
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      functions program (receipt.admitted_entry wellFormed).original size := by
  have meaning := CallableRuntimeBodyMutualMeaning.Stateful.preserves_at
    (fun (_ : Unit) => CallableRuntimeBodyStaticOrigins.named true receipt.profile receipt.escaped)
    functions extension program faithful observations (protocol headers keys)
    (fun _ => CallableIndexedOwnedAllocationProducer.StableOwner keys)
    (fun _ => marked (headers := headers) (keys := keys) (registry := registry) functions sameLayout)
    (fun _ => acquire (headers := headers) (keys := keys) (registry := registry) functions sameLayout)
    (administrativeTransport headers keys) (CallableIndexedOwnedOrdinaryAllocation.bindings headers keys)
    (by intro _ context valid budget child within below scope id lowered impossible; cases impossible)
    size ()
  intro outcome after trace
  exact meaning (receipt.admitted_entry wellFormed).original trace

include wellFormed sameLayout extension faithful observations functionTypes in
/-- The original native completion retains its own size and returns an
independently measured Source body at the same actual parameter entry. -/
theorem parameter_reflects [FunctionCalls.FaultTokens faults] (size : Nat) :
    CallableRuntimeBodyEntryContracts.ReflectsAt (registry := registry) (faults := faults)
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      functions program (receipt.admitted_entry wellFormed).original size := by
  have meaning := CallableRuntimeBodyMutualMeaning.Stateful.reflects_at
    (fun (_ : Unit) => CallableRuntimeBodyStaticOrigins.named true receipt.profile receipt.escaped)
    functions extension program faithful observations functionTypes (protocol headers keys)
    (fun _ => CallableIndexedOwnedAllocationProducer.StableOwner keys)
    (fun _ => marked (headers := headers) (keys := keys) (registry := registry) functions sameLayout)
    (fun _ => acquire (headers := headers) (keys := keys) (registry := registry) functions sameLayout)
    (administrativeTransport headers keys) (CallableIndexedOwnedOrdinaryAllocation.bindings headers keys)
    (by intro _ context valid budget child within below scope id lowered impossible; cases impossible)
    size ()
  intro value finalStore completed
  exact meaning (receipt.admitted_entry wellFormed).original completed

include wellFormed sameLayout extension faithful observations in
/-- Every callback is derived at its actual receipt; the original continuation
agreement remains part of the production interface. -/
theorem source_bodies [FunctionCalls.FaultTokens faults] (budget : Nat) :
    CallableIndexedOwnedAdmittedNamedExpressionHeads.SourceBodiesFor
      (headers := headers) (keys := keys) (owner := owner) (functions := functions)
      (registry := registry) (faults := faults) (certificates := fun _ => noExpressions)
      (expressionSyntax := fun _ => noExpressionSyntax) (diagnosticPolicy := .reachable)
      (runtime := true) wellFormed header budget := by
  intro initial argumentsPool arguments actualReceipt _agreement size _smaller
  exact parameter_preserves functions owner actualReceipt wellFormed sameLayout extension faithful observations size

include wellFormed sameLayout extension faithful observations functionTypes in
/-- The real measured prefix and saved caller write select the same exact
native callback; no comparison to its reflected Source grade is used. -/
theorem native_bodies [FunctionCalls.FaultTokens faults] (budget : Nat) :
    CallableIndexedOwnedAdmittedNamedExpressionHeads.NativeBodiesFor
      (headers := headers) (keys := keys) (owner := owner) (functions := functions)
      (registry := registry) (faults := faults) (certificates := fun _ => noExpressions)
      (expressionSyntax := fun _ => noExpressionSyntax) (diagnosticPolicy := .reachable)
      (runtime := true) wellFormed header budget := by
  intro initial argumentsPool arguments actualReceipt prefixSize bodyStore value finalStore
    _prefixRun _prefixWithin _restored size _smaller
  exact parameter_reflects functions owner actualReceipt wellFormed sameLayout extension faithful observations functionTypes size

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedClosedNamedBodies
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedExpressionTreeBounds
/-! Admitted expression Trees close literal, builtin, composite, data, tuple
and genuine named ordinary/direct call children through the existing support
fold. Named callees have authentic static profiles with False expression
certificates and syntax: this bounded callee grammar supports accepted nil,
absent-let, block and return-unit forms. All call parameter/body callbacks are
proved internally at the real ParameterReceipt. No general mixed family or
indirect-call closure is claimed, and no execution law is an endpoint premise. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedExpressionTreeBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedClosedNamedBodies
open CallableIndexedOwnedExpressionHeads (Globals argumentProtocol)

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry}
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  {compilation : SourceCoreFunctions.Context}

/-- Canonical slots accompany the same actual full pool. The return operation
wraps that actual reached pool and changes none of its ordered records. -/
def caller : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
    (fun index => Globals (headers := headers) owner compilation.administrativePrefix index.scope index.canonical)
    (argumentProtocol (headers := headers) owner compilation.administrativePrefix) where
  pool := fun state => state.val
  records_eq := fun _ => rfl
  related := fun related => related
  slots := fun state => state.property
  restore := fun {_index} initial {_mapping _world _heap _store} reached _maps _worlds _frame _metadata related =>
    ⟨⟨reached, initial.property⟩, rfl, related⟩

variable {source : TypedSource} {context : SourceSemantics.Context} (evidence : Dynamic.EvidenceEnvironment)
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word} {fuel : Nat}
  {faults : FunctionCalls.FaultRep}
  (wellFormed : ProgramWellFormed program) (sourceRuntime : Dynamic.SourceRuntimeValid program context source)
  (covers : evidence.Covers context) (unique : NodeOccurrencesUnique source)
  (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup)
  (idsUnique : RequirementIdsUnique context)
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))
  (sameLayouts : ∀ header, header ∈ headers → header.layouts = compiled.indexed.layouts)
  (escaped : ∀ header, header ∈ headers → faults .controlEscapedFunction header.escaped)
  (profiles : ∀ header, header ∈ headers → CallableIndexedOwnedAdmittedNamedExpressionHeads.ProfilesFor
    (headers := headers) (owner := owner) (functions := functions) (registry := registry) (faults := faults)
    (certificates := fun _ => noExpressions) (expressionSyntax := fun _ => noExpressionSyntax)
    (diagnosticPolicy := .reachable) (runtime := true) header)

private abbrev calls : GenericExpressionMeaning.Certificate → GenericExpressionMeaning.Certificate :=
  RecursiveNamedCallEvidenceHeads.Calls (prepared := compiled.indexed.ancestry)
    (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    (some evidence) headers compilation source context

/-- The original full compiler Tree with ordinary literal receipts. -/
abbrev Tree : GenericExpressionMeaning.Certificate :=
  CompatibleExpressionCalls.Tree (calls (headers := headers) (compilation := compilation) (source := source) (context := context) evidence) fuel (.initial compiled.compatible.checked)
    source context solved reasonAt

/-- The same original Tree keeps exact selected runtime numeric receipts. -/
abbrev RuntimeTree : GenericExpressionMeaning.Certificate :=
  CompatibleExpressionCalls.Tree.WithLiterals (calls := calls (headers := headers) (compilation := compilation) (source := source) (context := context) evidence) (fuel := fuel)
    (values := .initial compiled.compatible.checked) (source := source) (context := context) (solved := solved)
    (reasonAt := reasonAt) (fun _ id lowered => CompatibleExpressionLiteralRuntime.Certificate solved source id lowered)

include extension faithful observations functionTypes wellFormed sourceRuntime covers unique owners idsUnique
  uninitialized missing sameLayouts escaped profiles in
private theorem preserves_with_literals [FunctionCalls.FaultTokens faults] {literals : GenericExpressionMeaning.Certificate}
    (literalMeaning : GenericExpressionMeaning.Preserves
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      program context evidence source literals faults) (size : Nat) :
    CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      (CallableIndexedOwnedIndirectCallerProtocol.forget_slots (caller (headers := headers) (compilation := compilation) owner))
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) context evidence source
      (CompatibleExpressionCalls.Tree.WithLiterals (calls := calls (headers := headers) (compilation := compilation) (source := source) (context := context) evidence) (fuel := fuel)
        (values := .initial compiled.compatible.checked) (source := source) (context := context) (solved := solved)
        (reasonAt := reasonAt) literals) faults size := by
  apply CallableIndexedOwnedAdmittedExpressionBounds.preserves_tree_at_with_literals
    functions (calls (headers := headers) (compilation := compilation) (source := source) (context := context) evidence) size size (Nat.le_refl _)
  · intro child _within
    exact CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt.of_stateful
      wellFormed sourceRuntime covers
      (ProtectedStateTransition.PreservesAt.of_administrative _ _ _ _ _ _ _ _
        (CallableIndexedOwnedCanonicalState.administrativeTransport owner compilation.administrativePrefix)
        (RecursiveNamedBoundedContracts.preserves_at_of_unbounded
          (ProtectedExpressionMeaning.preserves_of_typed _
            (CompatibleExpressionBuiltins.preserves_with_literals functions extension faithful observations functionTypes
              program evidence unique uninitialized missing literalMeaning)) child))
  · intro certificate child within children
    apply CallableIndexedOwnedAdmittedExpressionCallsHeads.preserves_at_with_calls
      (CallableIndexedOwnedIndirectCallerProtocol.forget_slots (caller (headers := headers) (compilation := compilation) owner))
      (CallableIndexedOwnedCanonicalState.administrativeTransport owner compilation.administrativePrefix)
      functions extension faithful observations functionTypes evidence unique missing wellFormed sourceRuntime covers
      (calls (headers := headers) (compilation := compilation) (source := source) (context := context) evidence) size child within children
    exact CallableIndexedOwnedAdmittedNamedExpressionHeads.preserves_at
      (functions := functions) (owner := owner) (runtime := true) evidence (caller (headers := headers) (compilation := compilation) owner) wellFormed sourceRuntime covers unique idsUnique
      sameLayouts escaped profiles owners size child within
      (fun smaller strict => children smaller (Nat.le_of_lt strict))
      (fun header member => source_bodies functions owner wellFormed (sameLayouts header member)
        extension faithful observations size)

include extension faithful observations functionTypes wellFormed sourceRuntime covers unique
  uninitialized missing sameLayouts escaped profiles in
private theorem reflects_with_literals [FunctionCalls.FaultTokens faults] {literals : GenericExpressionMeaning.Certificate}
    (literalMeaning : GenericExpressionMeaning.Reflects
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      program context evidence source literals faults) (size : Nat) :
    CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      (CallableIndexedOwnedIndirectCallerProtocol.forget_slots (caller (headers := headers) (compilation := compilation) owner))
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) context evidence source
      (CompatibleExpressionCalls.Tree.WithLiterals (calls := calls (headers := headers) (compilation := compilation) (source := source) (context := context) evidence) (fuel := fuel)
        (values := .initial compiled.compatible.checked) (source := source) (context := context) (solved := solved)
        (reasonAt := reasonAt) literals) faults size := by
  apply CallableIndexedOwnedAdmittedExpressionBounds.reflects_tree_at_with_literals
    functions (calls (headers := headers) (compilation := compilation) (source := source) (context := context) evidence) size size (Nat.le_refl _)
  · intro child _within
    exact CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt.of_stateful
      wellFormed sourceRuntime covers
      (ProtectedStateTransition.ReflectsAt.of_administrative _ _ _ _ _ _ _ _
        (CallableIndexedOwnedCanonicalState.administrativeTransport owner compilation.administrativePrefix)
        (RecursiveNamedBoundedContracts.reflects_at_of_unbounded
          (ProtectedExpressionMeaning.reflects_of_typed _
            (CompatibleExpressionBuiltins.reflects_with_literals functions extension faithful observations functionTypes
              program evidence uninitialized missing literalMeaning)) child))
  · intro certificate child within children
    apply CallableIndexedOwnedAdmittedExpressionCallsHeads.reflects_at_with_calls
      (CallableIndexedOwnedIndirectCallerProtocol.forget_slots (caller (headers := headers) (compilation := compilation) owner))
      (CallableIndexedOwnedCanonicalState.administrativeTransport owner compilation.administrativePrefix)
      functions extension faithful observations functionTypes evidence unique missing wellFormed sourceRuntime covers
      (calls (headers := headers) (compilation := compilation) (source := source) (context := context) evidence) size child within children
    exact CallableIndexedOwnedAdmittedNamedExpressionHeads.reflects_at
      (functions := functions) (owner := owner) (runtime := true) evidence (caller (headers := headers) (compilation := compilation) owner) wellFormed sourceRuntime covers unique
      sameLayouts escaped profiles size child within
      (fun smaller strict => children smaller (Nat.le_of_lt strict))
      (fun header member => native_bodies functions owner wellFormed (sameLayouts header member)
        extension faithful observations functionTypes size)

include extension faithful observations functionTypes wellFormed sourceRuntime covers unique owners idsUnique
  uninitialized missing sameLayouts escaped profiles in
/-- Genuine ordinary literal and callee-profile receipts close the whole
original Tree internally at every source size and actual admitted input. -/
theorem preserves_at [FunctionCalls.FaultTokens faults] (valid : CompatibleExpressionLiterals.ContextValid solved context evidence) (size : Nat) :
    CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      (CallableIndexedOwnedIndirectCallerProtocol.forget_slots (caller (headers := headers) (compilation := compilation) owner))
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      context evidence source (Tree (headers := headers) (compilation := compilation) (source := source) (context := context) (solved := solved) (reasonAt := reasonAt) (fuel := fuel) evidence) faults size := by
  intro scope id lowered tree
  exact preserves_with_literals functions extension faithful observations functionTypes owner evidence wellFormed
    sourceRuntime covers unique owners idsUnique uninitialized missing sameLayouts escaped profiles
    (CompatibleExpressionLiterals.preserves functions program context evidence valid unique faults) size
    ⟨tree, tree.literalSites⟩

include extension faithful observations functionTypes wellFormed sourceRuntime covers unique
  uninitialized missing sameLayouts escaped profiles in
/-- Native completion returns its independent Source size and the same actual
reached caller with successful admission; no Source trace is assumed. -/
theorem reflects_at [FunctionCalls.FaultTokens faults] (valid : CompatibleExpressionLiterals.ContextValid solved context evidence) (size : Nat) :
    CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      (CallableIndexedOwnedIndirectCallerProtocol.forget_slots (caller (headers := headers) (compilation := compilation) owner))
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      context evidence source (Tree (headers := headers) (compilation := compilation) (source := source) (context := context) (solved := solved) (reasonAt := reasonAt) (fuel := fuel) evidence) faults size := by
  intro scope id lowered tree
  exact reflects_with_literals functions extension faithful observations functionTypes owner evidence wellFormed
    sourceRuntime covers unique uninitialized missing sameLayouts escaped profiles
    (CompatibleExpressionLiterals.reflects functions program context evidence valid source faults) size
    ⟨tree, tree.literalSites⟩

include extension faithful observations functionTypes wellFormed sourceRuntime covers unique owners idsUnique
  uninitialized missing sameLayouts escaped profiles in
/-- Runtime numeric leaves use their exact original selected ledger rows. -/
theorem preserves_at_runtime [FunctionCalls.FaultTokens faults] (sameLedger : context.solvedRequirements = solved)
    (runtimeLedger : RuntimeRequirementLedgerValid context) (size : Nat) :
    CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      (CallableIndexedOwnedIndirectCallerProtocol.forget_slots (caller (headers := headers) (compilation := compilation) owner))
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      context evidence source (RuntimeTree (headers := headers) (compilation := compilation) (source := source) (context := context) (solved := solved) (reasonAt := reasonAt) (fuel := fuel) evidence) faults size :=
  preserves_with_literals functions extension faithful observations functionTypes owner evidence wellFormed
    sourceRuntime covers unique owners idsUnique uninitialized missing sameLayouts escaped profiles
    (CompatibleExpressionLiteralRuntime.preserves functions program context evidence sameLedger runtimeLedger unique faults) size

include extension faithful observations functionTypes wellFormed sourceRuntime covers unique
  uninitialized missing sameLayouts escaped profiles in
/-- Runtime reflection retains independent Source and native grades and every
original ledger row beside its actual returned pool. -/
theorem reflects_at_runtime [FunctionCalls.FaultTokens faults] (sameLedger : context.solvedRequirements = solved)
    (runtimeLedger : RuntimeRequirementLedgerValid context) (size : Nat) :
    CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      (CallableIndexedOwnedIndirectCallerProtocol.forget_slots (caller (headers := headers) (compilation := compilation) owner))
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      context evidence source (RuntimeTree (headers := headers) (compilation := compilation) (source := source) (context := context) (solved := solved) (reasonAt := reasonAt) (fuel := fuel) evidence) faults size :=
  reflects_with_literals functions extension faithful observations functionTypes owner evidence wellFormed
    sourceRuntime covers unique uninitialized missing sameLayouts escaped profiles
    (CompatibleExpressionLiteralRuntime.reflects functions program context evidence sameLedger runtimeLedger source faults) size

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedExpressionTreeBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedExpressionSequenceFaultBounds
/-! The original ready sequence consumes actual admitted child fault packets.
Finite Source joins retain the exact reason, token and reached tuple. No
primitive is selected from a category relation or an unrelated receiving heap. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedExpressionSequenceFaultBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open DataPatternValues DataExpressionSequence CallableIndexedOwnedFunctionState
open CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
open ExpressionFailurePostContracts
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment}
  (model : GenericHeap.PayloadModel catalog projects definitions)
  (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource)
  (certificate : GenericExpressionMeaning.Certificate) (faults : GenericExpressionMeaning.FaultRep)

def PreservesAt (post : ExpressionFailurePostContracts.ExpressionFaultPost) (size : Nat) : Prop :=
  ∀ {scope id lowered}, certificate scope id lowered →
  ∀ {node}, source.lookupExpression? id = some node → ExpressionHasType source context id node.type →
  ∀ {mapping world administrativeContext environment canonical actual actualContext before store ξ outcome after},
    DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions →
    GenericHeap.HeapRepresents model mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree ξ canonical actual → RuntimeEnvironmentHasTypes world actual actualContext definitions →
  ∀ initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩,
    Admission bridge context initial →
    RecursiveNamedCallBounds.ExpressionOutcome program size context evidence source environment before id outcome after →
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (lowered.expression.rename ξ) value finalStore ∧
      GenericExpressionMeaning.ResultRepresents model finalMap finalWorld node.type lowered.type faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ PostAdmission bridge context node.type outcome reached ∧
        CallableIndexedOwnedAdmittedBuiltinFaultBounds.NativeFaultAt (program := program) (source := source)
          (context := context) evidence post initial environment id lowered actual ξ outcome reached

def ReflectsAt (post : ExpressionFailurePostContracts.ExpressionFaultPost) (size : Nat) : Prop :=
  ∀ {scope id lowered}, certificate scope id lowered →
  ∀ {node}, source.lookupExpression? id = some node → ExpressionHasType source context id node.type →
  ∀ {mapping world administrativeContext environment canonical actual actualContext before store ξ value finalStore},
    DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions →
    GenericHeap.HeapRepresents model mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree ξ canonical actual → RuntimeEnvironmentHasTypes world actual actualContext definitions →
  ∀ initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩,
    Admission bridge context initial →
    EvaluationSize size actual store (lowered.expression.rename ξ) value finalStore →
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.ExpressionOutcome program sourceSize context evidence source environment before id outcome after ∧
      GenericExpressionMeaning.ResultRepresents model finalMap finalWorld node.type lowered.type faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ PostAdmission bridge context node.type outcome reached ∧
        CallableIndexedOwnedAdmittedBuiltinFaultBounds.NativeFaultAt (program := program) (source := source)
          (context := context) evidence post initial environment id lowered actual ξ outcome reached

variable {bridge model context evidence source certificate faults}

theorem PreservesAt.forget {post : ExpressionFaultPost} {size : Nat}
    (meaning : PreservesAt bridge model context evidence source certificate faults post size) :
    CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge model context evidence source certificate faults size := by
  intro scope id lowered certified node found sourceTyped mapping world admin environment canonical actual actualContext
    before store ξ outcome after environments heaps locals agrees typed initial admitted trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
    maps, worlds, frame, metadata, reached, related, admission, _post⟩ :=
    meaning certified found sourceTyped environments heaps locals agrees typed initial admitted trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
    maps, worlds, frame, metadata, reached, related, admission⟩

theorem ReflectsAt.forget {post : ExpressionFaultPost} {size : Nat}
    (meaning : ReflectsAt bridge model context evidence source certificate faults post size) :
    CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt bridge model context evidence source certificate faults size := by
  intro scope id lowered certified node found sourceTyped mapping world admin environment canonical actual actualContext
    before store ξ value finalStore environments heaps locals agrees typed initial admitted trace
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
    maps, worlds, frame, metadata, reached, related, admission, _post⟩ :=
    meaning certified found sourceTyped environments heaps locals agrees typed initial admitted trace
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
    maps, worlds, frame, metadata, reached, related, admission⟩

variable (bridge model context evidence source certificate faults)
variable {ids : List ExpressionId} {sourceTypes originalSourceTypes : List TypeSystem.Ty}

theorem preserves_child_at (post : ExpressionFaultPost) {id : ExpressionId} {size : Nat}
    (unique : NodeOccurrencesUnique source) (typing : ExpressionsHaveTypes source context ids originalSourceTypes)
    (member : id ∈ ids)
    (meaning : PreservesAt bridge model context evidence source certificate faults post size) :
    ProtectedReadyExpressionFaultPostContracts.ExpressionPreservesAt ProtectedDataExpressionSequence.ExpressionTraceAt callerProtocol
      (Admission bridge context) post size model program context evidence source
      (fun current expression code => expression = id ∧ certificate current expression code) faults := by
  intro scope expression lowered certified node found mapping world admin environment canonical actual actualContext
    before store ξ outcome after environments heaps locals agrees typed initial admitted trace
  have sourceTyped := CallableIndexedOwnedAdmittedExpressionSequence.member_expression_typed unique typing (certified.1.symm ▸ member) found
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
      maps, worlds, frame, metadata, reached, related, admission, retained⟩ :=
    meaning certified.2 found sourceTyped environments heaps locals agrees typed initial admitted
      (ProtectedStateTransition.SequenceBridge.call_trace trace)
  refine ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
    maps, worlds, frame, metadata, ⟨reached, related, ?_⟩, ?_⟩
  · intro value same
    cases same
    exact admission.at_value.2
  · cases outcome with
    | value => trivial
    | fault reason =>
      exact CallableIndexedOwnedAdmittedBuiltinFaultBounds.NativeFaultAt.at_fault retained evaluated

/-- Native reflection keeps its independent Source grade and actual post. -/
theorem reflects_child_at (post : ExpressionFaultPost) {id : ExpressionId} {size : Nat}
    (unique : NodeOccurrencesUnique source) (typing : ExpressionsHaveTypes source context ids originalSourceTypes)
    (member : id ∈ ids)
    (meaning : ReflectsAt bridge model context evidence source certificate faults post size) :
    ProtectedReadyExpressionFaultPostContracts.ExpressionReflectsAt ProtectedDataExpressionSequence.ExpressionTraceAt callerProtocol
      (Admission bridge context) post size model program context evidence source
      (fun current expression code => expression = id ∧ certificate current expression code) faults := by
  intro scope expression lowered certified node found mapping world admin environment canonical actual actualContext
    before store ξ value finalStore environments heaps locals agrees typed initial admitted completed
  have sourceTyped := CallableIndexedOwnedAdmittedExpressionSequence.member_expression_typed unique typing (certified.1.symm ▸ member) found
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
      maps, worlds, frame, metadata, reached, related, admission, retained⟩ :=
    meaning certified.2 found sourceTyped environments heaps locals agrees typed initial admitted completed
  refine ⟨sourceSize, outcome, after, finalMap, finalWorld,
    ProtectedStateTransition.SequenceBridge.source_trace trace, represented, finalHeaps,
    maps, worlds, frame, metadata, ⟨reached, related, ?_⟩, ?_⟩
  · intro value same
    cases same
    exact admission.at_value.2
  · cases outcome with
    | value => trivial
    | fault reason =>
      exact CallableIndexedOwnedAdmittedBuiltinFaultBounds.NativeFaultAt.at_fault retained completed.sound

variable {scope : SourceCoreLocalCell.Scope} {codes : List SourceCoreBasic.LoweredExpr}

theorem preserves_fault_bounded (expressionPost : ExpressionFaultPost) (listPost : ExpressionsFaultPost)
    (joins : SequenceJoins expressionPost listPost program context evidence source) (budget : Nat) (tree : Tree source certificate scope ids sourceTypes codes)
    (unique : NodeOccurrencesUnique source)
    (typing : ExpressionsHaveTypes source context ids originalSourceTypes)
    (meaning : ∀ size, size < budget →
      PreservesAt bridge model context evidence source certificate faults expressionPost size)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {reason : Dynamic.SemanticFault}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext definitions)
    (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (initialReady : Admission bridge context initial)
    {size : Nat}
    (execution : SourceExecutionSize.ExpressionsFault program size context evidence source environment before ids reason after) (bounded : size ≤ budget) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ)
        (.inLeft (SourceCoreCalls.packArguments codes).type (.word token)) finalStore ∧
      faults reason token ∧ GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ StableRows (bridge.pool reached) ∧
        listPost program context evidence source environment before ids reason after token finalMap finalWorld finalStore := by
  obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps,
    maps, worlds, frame, metadata, ⟨reached, related⟩, retained⟩ :=
    ProtectedDataExpressionSequence.Stateful.WithReady.preserves_fault_bounded_with_post callerProtocol
      (Admission bridge context) expressionPost listPost joins budget tree
      (fun id member size smaller => preserves_child_at bridge model context evidence source certificate faults
        expressionPost unique typing member (meaning size smaller))
      environments heaps locals layout actualTyped initial initialReady execution bounded
  exact ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps,
    maps, worlds, frame, metadata, reached, related,
    StableRows.after_administrative (bridge.pool initial) (bridge.pool reached) initialReady.rows frame, retained⟩

theorem reflects_bounded (expressionPost : ExpressionFaultPost) (listPost : ExpressionsFaultPost)
    (joins : SequenceJoins expressionPost listPost program context evidence source) (budget : Nat) (tree : Tree source certificate scope ids sourceTypes codes)
    (unique : NodeOccurrencesUnique source)
    (typing : ExpressionsHaveTypes source context ids originalSourceTypes)
    (meaning : ∀ size, size < budget →
      ReflectsAt bridge model context evidence source certificate faults expressionPost size)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {value : Value}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext definitions)
    (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (initialReady : Admission bridge context initial)
    {size : Nat}
    (evaluated : EvaluationSize size actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ) value finalStore) (bounded : size < budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      ProtectedDataExpressionSequence.TraceAt program sourceSize context evidence source environment before ids outcome after ∧
      Result model finalMap finalWorld sourceTypes codes faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ CallableIndexedOwnedAdmittedExpressionSequence.PostSequenceAdmission bridge (context := context) outcome reached ∧
        ListOutcomePost listPost program context evidence source environment before ids
          (SourceCoreCalls.packArguments codes).type outcome after value finalMap finalWorld finalStore := by
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
    maps, worlds, frame, metadata, ⟨reached, related, successful⟩, retained⟩ :=
    ProtectedDataExpressionSequence.Stateful.WithReady.reflects_bounded_with_post callerProtocol
      (Admission bridge context) expressionPost listPost joins budget tree
      (fun id member size smaller => reflects_child_at bridge model context evidence source certificate faults
        expressionPost unique typing member (meaning size smaller))
      environments heaps locals layout actualTyped initial initialReady evaluated bounded
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
    maps, worlds, frame, metadata, reached, related,
    ⟨StableRows.after_administrative (bridge.pool initial) (bridge.pool reached) initialReady.rows frame, successful⟩, retained⟩

theorem preserves_bounded (expressionPost : ExpressionFaultPost) (listPost : ExpressionsFaultPost)
    (joins : SequenceJoins expressionPost listPost program context evidence source) (budget : Nat) (tree : Tree source certificate scope ids sourceTypes codes)
    (unique : NodeOccurrencesUnique source)
    (typing : ExpressionsHaveTypes source context ids originalSourceTypes)
    (meaning : ∀ size, size < budget →
      PreservesAt bridge model context evidence source certificate faults expressionPost size)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {outcome : Outcome}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext definitions)
    (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (initialReady : Admission bridge context initial)
    {size : Nat}
    (execution : ProtectedDataExpressionSequence.TraceAt program size context evidence source environment before ids outcome after) (bounded : size ≤ budget) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ) value finalStore ∧
      Result model finalMap finalWorld sourceTypes codes faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ CallableIndexedOwnedAdmittedExpressionSequence.PostSequenceAdmission bridge (context := context) outcome reached ∧
        ListOutcomePost listPost program context evidence source environment before ids
          (SourceCoreCalls.packArguments codes).type outcome after value finalMap finalWorld finalStore := by
  cases execution with
  | values trace =>
    obtain ⟨values, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
      maps, worlds, frame, metadata, reached, related, admitted⟩ :=
      CallableIndexedOwnedAdmittedExpressionSequence.preserves_values_bounded bridge budget tree unique typing
        (fun size smaller => PreservesAt.forget (meaning size smaller)) environments heaps locals layout actualTyped initial initialReady trace bounded
    exact ⟨_, finalStore, finalMap, finalWorld, evaluated, .values represented, finalHeaps,
      maps, worlds, frame, metadata, reached, related, ⟨admitted.rows, fun _ _ => admitted⟩, True.intro⟩
  | fault trace =>
    obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps,
      maps, worlds, frame, metadata, reached, related, rows, retained⟩ :=
      preserves_fault_bounded bridge model context evidence source certificate faults expressionPost listPost joins
        budget tree unique typing meaning environments heaps locals layout actualTyped initial initialReady trace bounded
    exact ⟨_, finalStore, finalMap, finalWorld, evaluated, .fault matched, finalHeaps,
      maps, worlds, frame, metadata, reached, related, ⟨rows, fun _ impossible => nomatch impossible⟩,
      ⟨token, rfl, retained⟩⟩

section Builtin
variable (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry}
  (transport : ProtectedStateTransition.AdministrativeTransport callerProtocol)
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word} {fuel : Nat}
  (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
  (reads : ReachedLoweredReadOutcomePorts.ReadPolicies fuel (.initial compiled.compatible.checked) source context reasonAt faults)
  (missing : IndexFaultPostContracts.MissingPolicies (.initial compiled.compatible.checked) source functions registry
    program context evidence reasonAt faults)
  (unique : NodeOccurrencesUnique source)
  (wellFormed : ProgramWellFormed program) (runtime : Dynamic.SourceRuntimeValid program context source)
  (covers : evidence.Covers context)

include transport extension faithful observations functionTypes valid reads missing unique wellFormed runtime covers in
/-- The genuine builtin producer supplies the closed child packet at every
actual admitted entry. The finite conversion supplies no separate origin law. -/
theorem preserves_builtin [FunctionCalls.FaultTokens faults] (size : Nat) :
    PreservesAt bridge (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      context evidence source (CompatibleExpressionBuiltins.Tree fuel (.initial compiled.compatible.checked)
        source context solved reasonAt) faults
      (ReachedBuiltinExpressionFaultPaths.model_expressionPost compiled.compatible.checked functions registry) size := by
  intro scope id lowered tree node found sourceTyped mapping world administrative environment canonical actual actualContext
    before store ξ outcome after environments heaps locals agrees typed initial admitted trace
  exact CallableIndexedOwnedAdmittedBuiltinFaultBounds.preserves bridge functions evidence transport extension
    faithful observations functionTypes valid reads missing unique wellFormed runtime covers
    tree found sourceTyped environments heaps locals agrees typed initial admitted trace

include transport extension faithful observations functionTypes valid reads missing unique wellFormed runtime covers in
/-- The actual measured builtin child retains its independent Source grade
and the same token/path used by the ordered sequence join. -/
theorem reflects_builtin [FunctionCalls.FaultTokens faults] (size : Nat) :
    ReflectsAt bridge (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      context evidence source (CompatibleExpressionBuiltins.Tree fuel (.initial compiled.compatible.checked)
        source context solved reasonAt) faults
      (ReachedBuiltinExpressionFaultPaths.model_expressionPost compiled.compatible.checked functions registry) size := by
  intro scope id lowered tree node found sourceTyped mapping world administrative environment canonical actual actualContext
    before store ξ value finalStore environments heaps locals agrees typed initial admitted completed
  exact CallableIndexedOwnedAdmittedBuiltinFaultBounds.reflects bridge functions evidence transport extension
    faithful observations functionTypes valid reads missing unique wellFormed runtime covers
    tree found sourceTyped environments heaps locals agrees typed initial admitted completed

/-- The concrete builtin list post uses the original head/tail path constructors
at the same primitive, without a generic category-wide origin supplier. -/
theorem builtin_sequence_joins :
    SequenceJoins
      (ReachedBuiltinExpressionFaultPaths.model_expressionPost compiled.compatible.checked functions registry)
      (ReachedBuiltinExpressionFaultPaths.model_expressionsPost compiled.compatible.checked functions registry)
      program context evidence source :=
  ReachedBuiltinExpressionFaultPaths.sequence_joins compiled.compatible.checked functions registry program context evidence source

end Builtin

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedExpressionSequenceFaultBounds
end
