import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNativeDirectCellOrigins
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedLambdaProtocolPackets
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedTypedLambdaInvocationBounds

/-! A direct prepared closure retains its actual Code, captured runtime
fields and one native-collected JointBody. Its own Source metadata and runtime
typing construct the value model; no universal CatalogSites projection is used.
Actual Entry/Prefix packets feed one strict same-body protocol flow child. The
original invocation and application restore the actual caller once, while the
receiving registry stays independent of the preparation registry. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedDirectLambdaInvocationBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open CallableIndexedOwnedFunctionValues (Header Key)
open CallableIndexedOwnedPreparedNativeDirectCellOrigins (Association)
open CallableIndexedOwnedPreparedContextualQualification (Facet)
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
open RecursiveNamedCatalogInvocationBounds (Below)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {qualification : Facet compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {mapping : LocationMap} {world : StoreTyping}
  {function : Dynamic.Closure} {native : Value}
  {bindings : List CallableIndexedParameterCertificates.Binding} {parameterCore resultCore : Ty}
  (functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed))

/-- The selected ordinary body uses its actual Header/Nested packet; the
selected method body uses its actual Named/Origin packet. Both are the exact
prepared JointBody projection stored beside the compiler qualification. -/
def FlowPreserves
    (member : Association qualification headers keys bodyRegistry faults
    mapping world function native bindings parameterCore resultCore) (size : Nat) : Prop :=
  match member with
  | .ordinary owner captured code history support _origin _prepared _qualified prefixContext globals _reference _typed =>
    CallableIndexedOwnedTypedLambdaProtocolContinuations.FlowPreserves captured code support.body.toBody functions
        (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner support.caller)
        (registry := registry) (faults := faults) size
  | .principal owner captured code history support _origin _prepared _qualified globals leading _reference _typed =>
    CallableIndexedOwnedTypedLambdaProtocolContinuations.FlowPreserves captured code support.body.toBody functions
        (CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner support.principal.named)
        (registry := registry) (faults := faults) size

/-- Native flow is indexed by the same selected packet protocol and original
body. Its measured grade remains independent of the reconstructed Source grade. -/
def FlowReflects
    (member : Association qualification headers keys bodyRegistry faults
    mapping world function native bindings parameterCore resultCore) (size : Nat) : Prop :=
  match member with
  | .ordinary owner captured code history support _origin _prepared _qualified prefixContext globals _reference _typed =>
    CallableIndexedOwnedTypedLambdaProtocolContinuations.FlowReflects captured code support.body.toBody functions
        (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner support.caller)
        (registry := registry) (faults := faults) size
  | .principal owner captured code history support _origin _prepared _qualified globals leading _reference _typed =>
    CallableIndexedOwnedTypedLambdaProtocolContinuations.FlowReflects captured code support.body.toBody functions
        (CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner support.principal.named)
        (registry := registry) (faults := faults) size

variable {before : Dynamic.Heap} {store : Store}
  {callerScope : SourceCoreLocalCell.Scope} {callerCanonical : Environment}
  (member : Association qualification headers keys bodyRegistry faults
    mapping world function native bindings parameterCore resultCore)
  (initial : State headers keys ⟨callerScope, mapping, world, before, store, callerCanonical⟩)
  {arguments : List Dynamic.Value} {nativeArguments : List Value}
  (represented : CallableIndexedParameterMeaning.Arguments
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
    mapping world bindings arguments nativeArguments)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions mapping world before store)
  (beforeTyped : Dynamic.HeapWellTyped function.context before)
  (argumentsTyped : Dynamic.ValuesHaveTypes function.context before arguments
    (function.parameters.map (fun binder => binder.scheme.body)))
  (locals : Dynamic.EnvironmentAgrees before function.context.locals function.captured)
  (stable : StableRows initial)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))

include represented heaps beforeTyped argumentsTyped locals stable wellFormed in
/-- Each actual branch constructs its genuine parameter packets and consumes
one strict protocol-flow child at the same retained body. The original low
invocation and finite apply edge retain the same restored caller pool. -/
theorem preserves_at (budget : Nat)
    (below : Below budget (FlowPreserves functions member (registry := registry)))
    {size : Nat} {callContext : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.CallOutcome (Program.ofChecked compiled.sourceProgram)
    size callContext callerEvidence function.evidence before (.closure function) arguments outcome after)
    (within : size ≤ budget) :
    ∃ value finalStore,
    Evaluates [native, DataPatternValues.packValues nativeArguments] store
        CallableIndexedLambdaCalls.applyPayload value finalStore ∧
    CallableIndexedOwnedStoredClosureInvocation.ResultAt (registry := registry) (faults := faults)
        functions initial function resultCore outcome after value finalStore := by
  cases member with
  | ordinary owner captured code history support origin prepared qualified prefixContext globals referenceIndex typed =>
    have raw : Dynamic.ValuesHaveTypes function.context before arguments support.body.types := by
        simpa only [Dynamic.MonoBindersExtend.bodyTypes_eq support.body.extended] using argumentsTyped
    obtain ⟨currentMetadata, currentCarried⟩ := stable owner.position
    have reference : captured.canonical[code.referenceIndex]? =
          some (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation) := by
        rw [referenceIndex]
        exact globals.reference
    change Below budget (CallableIndexedOwnedTypedLambdaProtocolContinuations.FlowPreserves
        captured code support.body.toBody functions
        (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner support.caller)
        (registry := registry) (faults := faults)) at below
    let packets := CallableIndexedOwnedPreparedLambdaProtocolPackets.Ordinary.packets
        (registry := registry) (arguments := arguments) (nativeArguments := nativeArguments)
        captured code history functions owner initial support origin globals prefixContext
    have continuation := CallableIndexedOwnedTypedLambdaProtocolContinuations.source_continuation
        captured code history support.body.toBody functions
        (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner support.caller)
        owner initial packets beforeTyped raw stable wellFormed budget below
    obtain ⟨value, finalStore, finalMap, finalWorld, invoked, result, finalHeaps, maps, worlds,
          frame, metadata, reached, related⟩ :=
        CallableIndexedOwnedLambdaInvocationBounds.invocation_preserves_bounded_at_with_continuation
          captured code history support.body.toBody.toContext functions represented owner initial
          heaps locals reference currentCarried (CallableIndexedLambdaTemplatePermission.lambda_allowed code history)
          budget continuation trace within
    exact ⟨value, finalStore, .apply (.second (.first (.var rfl))) (.var rfl) invoked,
        finalMap, finalWorld, result, finalHeaps, maps, worlds, frame, metadata, reached, related,
        StableRows.after_administrative initial reached stable frame⟩
  | principal owner captured code history support origin prepared qualified globals leading referenceIndex typed =>
    have raw : Dynamic.ValuesHaveTypes function.context before arguments support.body.types := by
        simpa only [Dynamic.MonoBindersExtend.bodyTypes_eq support.body.extended] using argumentsTyped
    obtain ⟨currentMetadata, currentCarried⟩ := stable owner.position
    have reference : captured.canonical[code.referenceIndex]? =
          some (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation) := by
        rw [referenceIndex]
        exact globals.reference
    change Below budget (CallableIndexedOwnedTypedLambdaProtocolContinuations.FlowPreserves
        captured code support.body.toBody functions
        (CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner support.principal.named)
        (registry := registry) (faults := faults)) at below
    let packets := CallableIndexedOwnedPreparedLambdaProtocolPackets.Principal.packets
        (registry := registry) (arguments := arguments) (nativeArguments := nativeArguments)
        captured code history functions owner initial support origin globals leading
    have continuation := CallableIndexedOwnedTypedLambdaProtocolContinuations.source_continuation
        captured code history support.body.toBody functions
        (CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner support.principal.named)
        owner initial packets beforeTyped raw stable wellFormed budget below
    obtain ⟨value, finalStore, finalMap, finalWorld, invoked, result, finalHeaps, maps, worlds,
          frame, metadata, reached, related⟩ :=
        CallableIndexedOwnedLambdaInvocationBounds.invocation_preserves_bounded_at_with_continuation
          captured code history support.body.toBody.toContext functions represented owner initial
          heaps locals reference currentCarried (CallableIndexedLambdaTemplatePermission.lambda_allowed code history)
          budget continuation trace within
    exact ⟨value, finalStore, .apply (.second (.first (.var rfl))) (.var rfl) invoked,
        finalMap, finalWorld, result, finalHeaps, maps, worlds, frame, metadata, reached, related,
        StableRows.after_administrative initial reached stable frame⟩

include represented heaps beforeTyped argumentsTyped locals stable wellFormed in
/-- The real application exposes one strictly smaller native invocation. Each
branch uses its authentic Prefix packet and native typed finish once; the
original restore returns that actual caller, with independent Source grade. -/
theorem reflects_at (budget : Nat)
    (below : Below budget (FlowReflects functions member (registry := registry)))
    {size : Nat} {callContext : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    {value : Value} {finalStore : Store}
    (completed : EvaluationSize size [native, DataPatternValues.packValues nativeArguments] store
    CallableIndexedLambdaCalls.applyPayload value finalStore)
    (within : size ≤ budget) :
    ∃ sourceSize outcome after,
    RecursiveNamedCallBounds.CallOutcome (Program.ofChecked compiled.sourceProgram)
        sourceSize callContext callerEvidence function.evidence before (.closure function) arguments outcome after ∧
    CallableIndexedOwnedStoredClosureInvocation.ResultAt (registry := registry) (faults := faults)
        functions initial function resultCore outcome after value finalStore := by
  cases member with
  | ordinary owner captured code history support origin prepared qualified prefixContext globals referenceIndex typed =>
    have raw : Dynamic.ValuesHaveTypes function.context before arguments support.body.types := by
        simpa only [Dynamic.MonoBindersExtend.bodyTypes_eq support.body.extended] using argumentsTyped
    obtain ⟨currentMetadata, currentCarried⟩ := stable owner.position
    have reference : captured.canonical[code.referenceIndex]? =
          some (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation) := by
        rw [referenceIndex]
        exact globals.reference
    change Below budget (CallableIndexedOwnedTypedLambdaProtocolContinuations.FlowReflects
        captured code support.body.toBody functions
        (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner support.caller)
        (registry := registry) (faults := faults)) at below
    let packets := CallableIndexedOwnedPreparedLambdaProtocolPackets.Ordinary.packets
        (registry := registry) (arguments := arguments) (nativeArguments := nativeArguments)
        captured code history functions owner initial support origin globals prefixContext
    have continuation := CallableIndexedOwnedTypedLambdaProtocolContinuations.native_continuation
        captured code history support.body.toBody functions
        (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner support.caller)
        owner initial packets beforeTyped raw stable wellFormed budget below
    obtain ⟨bodySize, smaller, applied⟩ := completed.apply_body (.second (.first (.var rfl))) (.var rfl)
    obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, result, finalHeaps, maps, worlds,
          frame, metadata, reached, related⟩ :=
        CallableIndexedOwnedLambdaInvocationBounds.invocation_reflects_bounded_at_with_continuation
          captured code history support.body.toBody.toContext functions represented owner initial
          heaps locals reference currentCarried (CallableIndexedLambdaTemplatePermission.lambda_allowed code history)
          support.body.frame budget continuation applied (Nat.le_trans (Nat.le_of_lt smaller) within)
    exact ⟨sourceSize, outcome, after, trace, finalMap, finalWorld, result, finalHeaps, maps, worlds,
        frame, metadata, reached, related, StableRows.after_administrative initial reached stable frame⟩
  | principal owner captured code history support origin prepared qualified globals leading referenceIndex typed =>
    have raw : Dynamic.ValuesHaveTypes function.context before arguments support.body.types := by
        simpa only [Dynamic.MonoBindersExtend.bodyTypes_eq support.body.extended] using argumentsTyped
    obtain ⟨currentMetadata, currentCarried⟩ := stable owner.position
    have reference : captured.canonical[code.referenceIndex]? =
          some (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation) := by
        rw [referenceIndex]
        exact globals.reference
    change Below budget (CallableIndexedOwnedTypedLambdaProtocolContinuations.FlowReflects
        captured code support.body.toBody functions
        (CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner support.principal.named)
        (registry := registry) (faults := faults)) at below
    let packets := CallableIndexedOwnedPreparedLambdaProtocolPackets.Principal.packets
        (registry := registry) (arguments := arguments) (nativeArguments := nativeArguments)
        captured code history functions owner initial support origin globals leading
    have continuation := CallableIndexedOwnedTypedLambdaProtocolContinuations.native_continuation
        captured code history support.body.toBody functions
        (CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner support.principal.named)
        owner initial packets beforeTyped raw stable wellFormed budget below
    obtain ⟨bodySize, smaller, applied⟩ := completed.apply_body (.second (.first (.var rfl))) (.var rfl)
    obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, result, finalHeaps, maps, worlds,
          frame, metadata, reached, related⟩ :=
        CallableIndexedOwnedLambdaInvocationBounds.invocation_reflects_bounded_at_with_continuation
          captured code history support.body.toBody.toContext functions represented owner initial
          heaps locals reference currentCarried (CallableIndexedLambdaTemplatePermission.lambda_allowed code history)
          support.body.frame budget continuation applied (Nat.le_trans (Nat.le_of_lt smaller) within)
    exact ⟨sourceSize, outcome, after, trace, finalMap, finalWorld, result, finalHeaps, maps, worlds,
        frame, metadata, reached, related, StableRows.after_administrative initial reached stable frame⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedDirectLambdaInvocationBounds
