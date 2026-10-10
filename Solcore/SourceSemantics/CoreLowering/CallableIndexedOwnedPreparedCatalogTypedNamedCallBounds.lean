import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedCatalogNamedBodyContinuations
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNamedArgumentAdmission
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedSequenceProducer

/-! Named expression leaves use the literal selected compiler profile at the
actual complete parameter entry. Its Prepared/HeaderAt, coupled extraction and
authentic diagnostic issuance stay available to strict body induction. Ordered
arguments establish Source admission before the original typed finish and
caller restoration. Zero capture prefix, genuine Header globals, static
profile/syntax construction and the shared strict flow family remain explicit
inputs. Ordinary and evidence-bearing named alternatives retain their original
caller dictionary and exact selected Header. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedCatalogTypedNamedCallBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory SourceCoreCallableIndexedFrames
open RecursiveNamedCatalog RecursiveNamedCatalogInvocationBounds
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
open CallableIndexedOwnedPreparedCatalogNamedProfiles (Profile)
open CallableIndexedOwnedPreparedCatalogNamedBodyContinuations (ProfilesFor FlowPreserves FlowReflects)
universe u
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (captureZero : owner.key.capturePrefix = 0)
  {certificates : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) → SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {expressionSyntax : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) → ExpressionId → Prop}

/-- This is the strict body induction input at the same static Header profile. -/
def SourceFlows (header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)) (budget : Nat) : Prop :=
  Below budget (fun child => ∀ administrative
    (profile : Profile (certificates := certificates)
      (expressionSyntax := expressionSyntax) header administrative),
    FlowPreserves (registry := registry) (faults := faults) (headers := headers) functions owner profile child)

/-- Native body size stays separate from the Source grade returned by finish. -/
def NativeFlows (header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)) (budget : Nat) : Prop :=
  Below budget (fun child => ∀ administrative
    (profile : Profile (certificates := certificates)
      (expressionSyntax := expressionSyntax) header administrative),
    FlowReflects (registry := registry) (faults := faults) (headers := headers) functions owner profile child)

section InvocationAdapters
variable {owner functions}
  {header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
  (globals : header.globals = compiled.indexed.base.globals.length)
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
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (sourceRuntime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context source)
  (covers : evidence.Covers context)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (argumentTypes : ExpressionsHaveTypes source context ids originalTypes)
  (application : SourceSemantics.DeclarationApplicationValid context header.instantiation originalTypes rawResult predicates)
  (profiles : ProfilesFor (headers := headers) (owner := owner) (functions := functions)
    (registry := registry) (certificates := certificates)
    (expressionSyntax := expressionSyntax) (header := header))
  (syntaxTree : GenericImperativeMatch.Syntax header.function.source (expressionSyntax header)
    header.context (.statements true header.function.body) header.function.resultType)

include captureZero globals admitted wellFormed sourceRuntime covers locals argumentTypes application profiles syntaxTree in
/-- Real Source argument execution and the authentic hook construct admission
for the exact reached parameter pool before a strict Source body is consumed. -/
theorem source_invocations (budget : Nat)
    (below : SourceFlows (headers := headers) (keys := keys) (owner := owner) (functions := functions)
      (registry := registry) (faults := faults) (certificates := certificates)
      (expressionSyntax := expressionSyntax) header budget) :
    CallableIndexedOwnedExpressionHeads.SourceInvocationsFor (source := source) (context := context)
      (evidence := evidence) (faults := faults) functions owner
      (CallableIndexedOwnedInvocationBounds.stableOwnerCondition (headers := headers) (keys := keys)
        (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix) functions registry header) bridge initial
      (environment := environment) (ids := ids) budget := by
  intro sourceSize arguments middle middleMap middleWorld middleStore payloads evaluated argumentState
    _argumentRelated _maps _worlds frame _metadata _capture represented _heaps
  have arity : header.function.parameters.length = arguments.length :=
    (congrArg List.length header.parameters).trans ((List.length_map Prod.fst).trans represented.length.1)
  have sourceAdmission := CallableIndexedOwnedNamedArgumentAdmission.at_successful_arguments header wellFormed
    sourceRuntime covers locals admitted.heap argumentTypes application evaluated.sound arity
  have stable := StableRows.after_administrative (bridge.pool initial) (bridge.pool argumentState) admitted.rows frame
  intro origin index metadata administrative actualContext actual ξ frameLocation
    physical selected history emitted entry agreement reached related allowed child strict outcome after trace
  exact CallableIndexedOwnedPreparedCatalogNamedBodyContinuations.source_continuation
    (functions := functions) (owner := owner) (caller := bridge.pool argumentState)
    (beforeTyped := sourceAdmission.1) (argumentsTyped := sourceAdmission.2) (stable := stable)
    (captureZero := captureZero) (globals := globals)
    (wellFormed := wellFormed) (profiles := profiles) (syntaxTree := syntaxTree) budget below physical selected history emitted entry agreement reached related allowed child strict trace

include captureZero globals admitted wellFormed sourceRuntime covers locals argumentTypes application profiles syntaxTree in
/-- Native arguments first recover their actual independently sized Source
trace; the same Source admission and parameter pool drive the strict body. -/
theorem native_invocations (budget : Nat)
    (below : NativeFlows (headers := headers) (keys := keys) (owner := owner) (functions := functions)
      (registry := registry) (faults := faults) (certificates := certificates)
      (expressionSyntax := expressionSyntax) header budget) :
    CallableIndexedOwnedExpressionHeads.NativeInvocationsFor (source := source) (context := context)
      (evidence := evidence) (faults := faults) functions owner
      (CallableIndexedOwnedInvocationBounds.stableOwnerCondition (headers := headers) (keys := keys)
        (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix) functions registry header) bridge initial
      (environment := environment) (ids := ids) budget := by
  intro sourceSize arguments middle middleMap middleWorld middleStore payloads evaluated argumentState
    _argumentRelated _maps _worlds frame _metadata _capture represented _heaps
  have arity : header.function.parameters.length = arguments.length :=
    (congrArg List.length header.parameters).trans ((List.length_map Prod.fst).trans represented.length.1)
  have sourceAdmission := CallableIndexedOwnedNamedArgumentAdmission.at_successful_arguments header wellFormed
    sourceRuntime covers locals admitted.heap argumentTypes application evaluated.sound arity
  have stable := StableRows.after_administrative (bridge.pool initial) (bridge.pool argumentState) admitted.rows frame
  intro origin index metadata administrative actualContext actual ξ frameLocation prefixSize bodyStore value finalStore
    physical selected history emitted _prefix within restored entry reached related allowed child strict bodyValue bodyFinalStore completed
  exact CallableIndexedOwnedPreparedCatalogNamedBodyContinuations.native_continuation
    (functions := functions) (owner := owner) (caller := bridge.pool argumentState)
    (beforeTyped := sourceAdmission.1) (argumentsTyped := sourceAdmission.2) (stable := stable)
    (captureZero := captureZero) (globals := globals)
    (wellFormed := wellFormed) (profiles := profiles) (syntaxTree := syntaxTree) budget below physical selected history emitted _prefix within restored entry reached related allowed child strict completed

end InvocationAdapters


section Heads
variable {owner functions}
  {source : TypedSource} {context : SourceSemantics.Context} (evidence : Dynamic.EvidenceEnvironment)
  {certificate : GenericExpressionMeaning.Certificate} {compilation : SourceCoreFunctions.Context}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
    (fun index => CallableIndexedOwnedExpressionHeads.Globals (headers := headers) owner compilation.administrativePrefix index.scope index.canonical) callerProtocol)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (sourceRuntime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context source)
  (covers : evidence.Covers context)
  (unique : NodeOccurrencesUnique source)
  (idsUnique : RequirementIdsUnique context)
  (sameLayouts : ∀ header, header ∈ headers → header.layouts = compiled.indexed.layouts)
  (globals : ∀ header, header ∈ headers → header.globals = compiled.indexed.base.globals.length)
  (syntaxTree : ∀ header, header ∈ headers →
    GenericImperativeMatch.Syntax header.function.source (expressionSyntax header)
      header.context (.statements true header.function.body) header.function.resultType)
  (profiles : ∀ header, header ∈ headers → ProfilesFor (headers := headers) (owner := owner) (functions := functions)
    (registry := registry) (certificates := certificates)
    (expressionSyntax := expressionSyntax) (header := header))
  (owners : ((Program.ofChecked compiled.sourceProgram).functions.map (fun definition => definition.body.owner)).Nodup)

include captureZero globals wellFormed sourceRuntime covers unique idsUnique sameLayouts syntaxTree profiles owners in
/-- Named ordinary/direct heads use the authentic Source argument row at their
actual input, then consume only a typed strict body at the real parameter post. -/
theorem preserves_at (budget size : Nat) (within : size ≤ budget)
    (children : RecursiveNamedBoundedContracts.Below budget
      (CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
        (CallableIndexedOwnedIndirectCallerProtocol.forget_slots bridge)
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        context evidence source certificate faults))
    (bodies : ∀ header, header ∈ headers → SourceFlows (headers := headers) (keys := keys) (owner := owner) (functions := functions)
      (registry := registry) (faults := faults) (certificates := certificates)
      (expressionSyntax := expressionSyntax) header budget) :
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
      (fun header => CallableIndexedOwnedInvocationBounds.stableOwnerCondition (headers := headers) (keys := keys)
        (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix) functions registry header)
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
        exact source_invocations (owner := owner) (functions := functions)
          (captureZero := captureZero) (globals := globals header member)
          bridge initial admitted wellFormed sourceRuntime covers locals argumentTypes application
          (profiles header member) (syntaxTree header member) budget (bodies header member)) trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
    maps, worlds, frame, metadata, reached, related,
    after_expression_sized initial reached admitted wellFormed sourceRuntime covers locals sourceTyped trace frame⟩

include captureZero globals wellFormed sourceRuntime covers unique sameLayouts syntaxTree profiles in
/-- Native heads retain the original native grade. The genuine reflected Source
argument and parent grades establish admission at their actual reached states. -/
theorem reflects_at (budget size : Nat) (within : size ≤ budget)
    (children : RecursiveNamedBoundedContracts.Below budget
      (CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
        (CallableIndexedOwnedIndirectCallerProtocol.forget_slots bridge)
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        context evidence source certificate faults))
    (bodies : ∀ header, header ∈ headers → NativeFlows (headers := headers) (keys := keys) (owner := owner) (functions := functions)
      (registry := registry) (faults := faults) (certificates := certificates)
      (expressionSyntax := expressionSyntax) header budget) :
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
      (fun header => CallableIndexedOwnedInvocationBounds.stableOwnerCondition (headers := headers) (keys := keys)
        (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix) functions registry header)
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
        exact native_invocations (owner := owner) (functions := functions)
          (captureZero := captureZero) (globals := globals header member)
          bridge initial admitted wellFormed sourceRuntime covers locals argumentTypes application
          (profiles header member) (syntaxTree header member) budget (bodies header member)) completed
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
    maps, worlds, frame, metadata, reached, related,
    after_expression_sized initial reached admitted wellFormed sourceRuntime covers locals sourceTyped trace frame⟩


/-- A selected dictionary must be the actual Source caller dictionary. -/
def CallerEvidence (selected : Option Dynamic.EvidenceEnvironment)
    (actual : Dynamic.EvidenceEnvironment) : Prop :=
  match selected with
  | none => True
  | some dictionary => dictionary = actual

include captureZero globals wellFormed sourceRuntime covers unique idsUnique sameLayouts syntaxTree profiles owners in
/-- The raw compiler's two named alternatives preserve their actual Header.
The optional dictionary is retained literally; no method Header is synthesized. -/
theorem preserves_calls (callerEvidence : Option Dynamic.EvidenceEnvironment)
    (sameEvidence : CallerEvidence callerEvidence evidence)
    (budget size : Nat) (within : size ≤ budget)
    (children : Below budget
      (CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
        (CallableIndexedOwnedIndirectCallerProtocol.forget_slots bridge)
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        context evidence source certificate faults))
    (bodies : ∀ header, header ∈ headers → SourceFlows (headers := headers) (keys := keys)
      (owner := owner) (functions := functions) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax)
      header budget) :
    CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      (CallableIndexedOwnedIndirectCallerProtocol.forget_slots bridge)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      context evidence source
      (RecursiveNamedCallEvidenceHeads.Calls (prepared := compiled.indexed.ancestry)
        (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        callerEvidence headers compilation source context certificate) faults size := by
  cases callerEvidence with
  | some dictionary =>
      cases sameEvidence
      exact preserves_at (functions := functions) (owner := owner)
        (captureZero := captureZero) (globals := globals) evidence bridge wellFormed sourceRuntime covers unique idsUnique
        sameLayouts syntaxTree profiles owners budget size within children bodies
  | none =>
      intro scope id lowered head
      exact preserves_at (functions := functions) (owner := owner)
        (captureZero := captureZero) (globals := globals) evidence bridge wellFormed sourceRuntime covers unique idsUnique
        sameLayouts syntaxTree profiles owners budget size within children bodies
        (RecursiveNamedCallEvidenceHeads.Head.ordinary head)

include captureZero globals wellFormed sourceRuntime covers unique sameLayouts syntaxTree profiles in
/-- Native named completion retains the independent Source grade and actual
restored pool in either authentic optional-evidence alternative. -/
theorem reflects_calls (callerEvidence : Option Dynamic.EvidenceEnvironment)
    (sameEvidence : CallerEvidence callerEvidence evidence)
    (budget size : Nat) (within : size ≤ budget)
    (children : Below budget
      (CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
        (CallableIndexedOwnedIndirectCallerProtocol.forget_slots bridge)
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        context evidence source certificate faults))
    (bodies : ∀ header, header ∈ headers → NativeFlows (headers := headers) (keys := keys)
      (owner := owner) (functions := functions) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax)
      header budget) :
    CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      (CallableIndexedOwnedIndirectCallerProtocol.forget_slots bridge)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      context evidence source
      (RecursiveNamedCallEvidenceHeads.Calls (prepared := compiled.indexed.ancestry)
        (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        callerEvidence headers compilation source context certificate) faults size := by
  cases callerEvidence with
  | some dictionary =>
      cases sameEvidence
      exact reflects_at (functions := functions) (owner := owner)
        (captureZero := captureZero) (globals := globals) evidence bridge wellFormed sourceRuntime covers unique
        sameLayouts syntaxTree profiles budget size within children bodies
  | none =>
      intro scope id lowered head
      exact reflects_at (functions := functions) (owner := owner)
        (captureZero := captureZero) (globals := globals) evidence bridge wellFormed sourceRuntime covers unique
        sameLayouts syntaxTree profiles budget size within children bodies
        (RecursiveNamedCallEvidenceHeads.Head.ordinary head)

end Heads
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedCatalogTypedNamedCallBounds
