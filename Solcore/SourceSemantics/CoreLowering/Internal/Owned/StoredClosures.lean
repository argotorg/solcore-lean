import Solcore.SourceSemantics.CoreLowering.Internal.Owned.LambdaReadyFamilies
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.ReadyContinuations
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.BodyReadyState
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.ProfileExtraction
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.IndexedParameters
import Solcore.SourceSemantics.CoreLowering.DataExpressionSequence
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.RuntimeIndirectCalls
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.ExpressionConstructors
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.IndexedLambdaTyping
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.IndirectExpressionHeads
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedAdmitted.LexicalBodies
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.RuntimeBodies
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.ReadyExpressions
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedAdmitted.ExpressionTrees
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedAdmitted.StagedExpressions

/-!
# Owned callables: stored closures

Invocation, arguments and association of stored closures, stored function models, and extended joint ready families.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedExtendedJointReadyFamilyInputs
/-! This additive static union preserves all frozen joint branches. Genuine
method-generated lambdas use their trait-principal packets; named nested
entries retain their real Source seed, bundle and frame. Actual mixed
expression dispatch remains a separate strict measured obligation. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedExtendedJointReadyFamilyInputs
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedOwnedFunctionState
open CallableIndexedOwnedAdmittedLexicalReadiness (readiness)
open CallableIndexedOwnedBodySourceOrigin (source_origin)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {certificates : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) →
    SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {expressionSyntax : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) → ExpressionId → Prop}

/-- Original branches are retained verbatim. Each additional index carries
its genuine full Source/compiler/principal receipts and exact packet protocol. -/
inductive Index where
  | existing (receipt : CallableIndexedOwnedJointReadyFamilyInputs.Index
      (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax))
  | methodLambda (receipt : CallableIndexedOwnedMethodLambdaReadyFamilyReceipts.Index
      (compiled := compiled) (keys := keys) (registry := registry) (faults := faults))
  | namedNested (receipt : CallableIndexedOwnedNamedNestedReadyFamilyReceipts.Index
      (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax) (diagnosticPolicy := .reachable) true)

/-- The complete original compiler origin is preserved branch by branch. -/
def base_origin (index : Index (headers := headers) (keys := keys) (registry := registry) (faults := faults)
    (certificates := certificates) (expressionSyntax := expressionSyntax)) :
    CallableRuntimeBodyOrigins.StaticOrigin (.initial compiled.compatible.checked)
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed) registry faults :=
  match index with
  | .existing receipt => CallableIndexedOwnedJointReadyFamilyInputs.base_origin receipt
  | .methodLambda receipt => receipt.support.origin receipt.escaped
  | .namedNested receipt => CallableRuntimeBodyStaticOrigins.named true receipt.receipt.profile receipt.receipt.escaped

/-- Runtime validity is the independent genuine Source receipt of that branch. -/
theorem sourceRuntime (index : Index (headers := headers) (keys := keys) (registry := registry) (faults := faults)
    (certificates := certificates) (expressionSyntax := expressionSyntax)) :
    Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram)
      (base_origin index).context (base_origin index).function.source := by
  cases index with
  | existing receipt => exact CallableIndexedOwnedJointReadyFamilyInputs.sourceRuntime receipt
  | methodLambda receipt => exact receipt.sourceRuntime
  | namedNested receipt => exact receipt.receipt.sourceRuntime

/-- The exact Source domain is strengthened without changing the compiled body. -/
def origin (index : Index (headers := headers) (keys := keys) (registry := registry) (faults := faults)
    (certificates := certificates) (expressionSyntax := expressionSyntax)) :=
  source_origin (base_origin index) (sourceRuntime index)

/-- Named slots, captured lambda packets and trait-principal packets remain
separate genuine protocols over the same full ordered pool representation. -/
def protocol (index : Index (headers := headers) (keys := keys) (registry := registry) (faults := faults)
    (certificates := certificates) (expressionSyntax := expressionSyntax)) :
    ProtectedStateTransition.Protocol (Records keys) :=
  match index with
  | .existing receipt => CallableIndexedOwnedJointReadyFamilyInputs.protocol receipt
  | .methodLambda receipt => CallableIndexedOwnedMethodLambdaReadyFamilyReceipts.body_protocol (headers := headers) receipt
  | .namedNested receipt => CallableIndexedOwnedNamedNestedReadyFamilyReceipts.body_protocol true receipt

/-- Each branch returns the identical underlying actual pool and records. -/
def bridge (index : Index (headers := headers) (keys := keys) (registry := registry) (faults := faults)
    (certificates := certificates) (expressionSyntax := expressionSyntax)) :
    CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) (protocol index) := by
  cases index with
  | existing receipt => exact CallableIndexedOwnedJointReadyFamilyInputs.bridge receipt
  | methodLambda receipt => exact CallableIndexedOwnedMethodLambdaReadyFamilyReceipts.bridge (headers := headers) receipt
  | namedNested receipt => exact CallableIndexedOwnedNamedNestedReadyFamilyReceipts.bridge true receipt

/-- Binding extension and restoration use each original actual protocol. -/
def bindings (index : Index (headers := headers) (keys := keys) (registry := registry) (faults := faults)
    (certificates := certificates) (expressionSyntax := expressionSyntax)) :
    ProtectedStateTransition.Bindings (protocol index) := by
  cases index with
  | existing receipt => exact CallableIndexedOwnedJointReadyFamilyInputs.bindings receipt
  | methodLambda receipt =>
    exact CallableIndexedOwnedOriginCanonicalState.bindings (headers := headers)
      receipt.owner receipt.support.principal.named
  | namedNested receipt =>
    exact CallableIndexedOwnedNestedCanonicalState.bindings (headers := headers)
      receipt.owner receipt.receipt.header

/-- Actual administrative effects preserve packet facets at that same post. -/
def transport (index : Index (headers := headers) (keys := keys) (registry := registry) (faults := faults)
    (certificates := certificates) (expressionSyntax := expressionSyntax)) :
    ProtectedStateTransition.AdministrativeTransport (protocol index) := by
  cases index with
  | existing receipt => exact CallableIndexedOwnedJointReadyFamilyInputs.transport receipt
  | methodLambda receipt =>
    exact CallableIndexedOwnedOriginCanonicalState.administrativeTransport (headers := headers)
      receipt.owner receipt.support.principal.named
  | namedNested receipt =>
    exact CallableIndexedOwnedNestedCanonicalState.administrativeTransport (headers := headers)
      receipt.owner receipt.receipt.header

variable (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (sameLayouts : ∀ header, header ∈ headers → header.layouts = compiled.indexed.layouts)

/-- Real marked allocation returns the exact reached protocol state; layout
casts use only authentic static equalities. -/
def producer (index : Index (headers := headers) (keys := keys) (registry := registry) (faults := faults)
    (certificates := certificates) (expressionSyntax := expressionSyntax)) :
    ProtectedStateTransition.MarkedAllocation.Producer (protocol index) (origin index).layouts (origin index).frameLayout
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) := by
  cases index with
  | existing receipt => exact CallableIndexedOwnedJointReadyFamilyInputs.producer functions sameLayouts receipt
  | methodLambda receipt =>
    exact CallableIndexedOwnedOriginCanonicalState.markedProducer (headers := headers)
      receipt.owner receipt.support.principal.named
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
  | namedNested receipt =>
    change ProtectedStateTransition.MarkedAllocation.Producer
      (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) receipt.owner receipt.receipt.header)
      receipt.receipt.header.layouts compiled.indexed.ancestry.layout.frame
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
    exact (sameLayouts receipt.receipt.header receipt.receipt.member).symm ▸
      CallableIndexedOwnedNestedCanonicalState.markedProducer (headers := headers)
        receipt.owner receipt.receipt.header
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)

private theorem ready_cast {stateProtocol : ProtectedStateTransition.Protocol (Records keys)}
    {first second : SourceCoreAllocationLayouts.Prepared} {firstFrame secondFrame : SourceCoreCallableIndexedFrames.Layout}
    {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment}
    {model : GenericHeap.PayloadModel catalog projects definitions}
    (layouts : first = second) (frame : firstFrame = secondFrame)
    (marked : ProtectedStateTransition.MarkedAllocation.Producer stateProtocol second secondFrame model)
    {location : Location} {native : NativeFrame}
    (ready : ProtectedStateTransition.OrdinaryAllocation.ReadyAt marked.toOrdinary location native) :
    ProtectedStateTransition.OrdinaryAllocation.ReadyAt
      ((layouts.symm ▸ frame.symm ▸ marked).toOrdinary) location native := by
  cases layouts
  cases frame
  exact ready

include functions sameLayouts in
/-- A genuine selected stable row supplies allocation readiness in the same
branch; no Source typing or canonical slots are inferred by this gate. -/
theorem acquire (index : Index (headers := headers) (keys := keys) (registry := registry) (faults := faults)
    (certificates := certificates) (expressionSyntax := expressionSyntax))
    (location : Location) (native : NativeFrame)
    (stable : CallableIndexedOwnedAllocationProducer.StableOwner keys location native) :
    ProtectedStateTransition.OrdinaryAllocation.ReadyAt (producer functions sameLayouts index).toOrdinary location native := by
  cases index with
  | existing receipt => exact CallableIndexedOwnedJointReadyFamilyInputs.acquire functions sameLayouts receipt location native stable
  | methodLambda receipt =>
    exact CallableIndexedOwnedOriginCanonicalState.readyAt_of_stableOwner (headers := headers)
      receipt.owner receipt.support.principal.named
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) stable
  | namedNested receipt =>
    exact ready_cast (sameLayouts receipt.receipt.header receipt.receipt.member) rfl _
      (CallableIndexedOwnedNestedCanonicalState.readyAt_of_stableOwner (headers := headers)
        receipt.owner receipt.receipt.header
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) stable)

variable (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))

/-- Genuine Source facts, static sites, actual allocation and snapshot
transfers build the existing finite catalog input fields internally. -/
def inputs (index : Index (headers := headers) (keys := keys) (registry := registry) (faults := faults)
    (certificates := certificates) (expressionSyntax := expressionSyntax)) :=
  CallableIndexedOwnedBodyReadyCatalog.inputs (bridge index) (base_origin index) (sourceRuntime index)
    (bindings index) wellFormed

variable (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)

include extension faithful observations sameLayouts in
/-- The sole family supplies these actual smaller expression results. The
finite head/loop recipes are proved internally at the exact indexed protocol. -/
theorem preserving_kits (index : Index (headers := headers) (keys := keys) (registry := registry) (faults := faults)
    (certificates := certificates) (expressionSyntax := expressionSyntax)) (budget : Nat)
    (expressions : ∀ context, (origin index).validity context →
      RecursiveNamedHeaderContracts.AtMost budget (fun size =>
        RecursiveNamedLexicalContracts.Stateful.WithReady.ExpressionPreservesAt (protocol index) (readiness (bridge index))
          (Program.ofChecked compiled.sourceProgram) (origin index).function.evidence
          (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
          (inputs wellFormed index).exprFacts ((origin index).certificates context)
          (source := (origin index).function.source) (context := context) (faults := faults) size)) :
    CallableRuntimeBodyReadyInputs.PreservingKits (protocol index) (readiness (bridge index)) (bindings index)
      (Program.ofChecked compiled.sourceProgram) (origin index) functions
      (CallableIndexedOwnedAllocationProducer.StableOwner keys) (inputs wellFormed index) budget :=
  CallableIndexedOwnedBodyReadyCatalog.preserving_ready_kits (bridge index) (base_origin index) (sourceRuntime index)
    (bindings index) wellFormed functions extension faithful observations (CallableIndexedOwnedAllocationProducer.StableOwner keys)
    (producer functions sameLayouts index) (acquire functions sameLayouts index) (transport index) budget expressions

include extension faithful observations sameLayouts in
/-- Native finite kits use the same original strict expression children and
return the same indexed witness; no joint body closure is asserted here. -/
theorem reflecting_kits (functionTypes : FunctionRuntimeViews functions)
    (index : Index (headers := headers) (keys := keys) (registry := registry) (faults := faults)
    (certificates := certificates) (expressionSyntax := expressionSyntax)) (budget : Nat)
    (expressions : ∀ context, (origin index).validity context →
      RecursiveNamedBoundedContracts.Below budget (fun size =>
        RecursiveNamedLexicalContracts.Stateful.WithReady.ExpressionReflectsAt (protocol index) (readiness (bridge index))
          (Program.ofChecked compiled.sourceProgram) (origin index).function.evidence
          (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
          (inputs wellFormed index).exprFacts ((origin index).certificates context)
          (source := (origin index).function.source) (context := context) (faults := faults) size)) :
    CallableRuntimeBodyReadyInputs.ReflectingKits (protocol index) (readiness (bridge index)) (bindings index)
      (Program.ofChecked compiled.sourceProgram) (origin index) functions
      (CallableIndexedOwnedAllocationProducer.StableOwner keys) (inputs wellFormed index) budget :=
  CallableIndexedOwnedBodyReadyCatalog.reflecting_ready_kits (bridge index) (base_origin index) (sourceRuntime index)
    (bindings index) wellFormed functions extension faithful observations (CallableIndexedOwnedAllocationProducer.StableOwner keys)
    (producer functions sameLayouts index) (acquire functions sameLayouts index) (transport index) budget functionTypes expressions

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedExtendedJointReadyFamilyInputs
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedExtendedJointLambdaReadyContinuations
/-! The actual selected lambda entry carries its genuine compiler layout.
Only that exact dependent index enters the extended joint family; no arbitrary static
lambda origin is assigned compiled layouts. Strict child results return the
same original reached pool and independently measured Source trace. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedExtendedJointLambdaReadyContinuations
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedOwnedFunctionState CallableIndexedLambdaValues
open CallableIndexedOwnedAdmittedLexicalReadiness (readiness)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {certificates : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) →
    SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {expressionSyntax : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) → ExpressionId → Prop}

variable {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
  {mapping : LocationMap} {world : StoreTyping} {capturedActual : Environment}
  (captured : Captures compiled.indexed mapping world scope function.captured capturedActual)
  (code : Code compiled.indexed function scope captured.administrative) (history : History code)
  (inputs : CallableIndexedLambdaEntryPrefix.Context (values := .initial compiled.compatible.checked) code)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  {arguments : List Dynamic.Value} {nativeArguments : List Value} {before : Dynamic.Heap} {store : Store}
  {callerScope : SourceCoreLocalCell.Scope} {callerCanonical : Environment}
  (caller : State headers keys ⟨callerScope, mapping, world, before, store, callerCanonical⟩)
  (body : CallableIndexedOwnedLambdaInvocationBounds.BodyOrigin (program := Program.ofChecked compiled.sourceProgram) code inputs registry faults)
  (beforeTyped : Dynamic.HeapWellTyped function.context before)
  (argumentsTyped : Dynamic.ValuesHaveTypes function.context before arguments inputs.types)
  (stable : CallableIndexedOwnedIndirectExpressionHeads.StableRows caller)
  (principal : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))
  (observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
    (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
    headers owner.key.locations 1 scope captured.canonical owner.key.frameLocation)
  (prefixContext : captured.administrative = RecursiveNamedLambdaFormationHeads.nativePrefix
    (indexed := compiled.indexed) (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram) principal)
  (sourceSeed : history.metadata = CallableIndexedNamedGeneration.state principal.named)
  (syntaxTree : GenericImperativeMatch.Syntax body.origin.function.source body.origin.expressionSyntax
    body.origin.context (.statements true body.origin.function.body) body.origin.function.resultType)

variable (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (layouts : body.origin.layouts = compiled.indexed.layouts)

include layouts wellFormed beforeTyped argumentsTyped stable observed prefixContext sourceSeed syntaxTree in
/-- Each authentic actual Source parameter entry constructs its index and
uses only the strict shared-family child in that index's exact protocol. -/
theorem source_continuation (budget : Nat)
    (below : ∀ index : CallableIndexedOwnedExtendedJointReadyFamilyInputs.Index
      (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax),
      RecursiveNamedBoundedContracts.Below budget
        (CallableRuntimeBodyReadyOrigins.PreservesAt (CallableIndexedOwnedExtendedJointReadyFamilyInputs.protocol index)
          (readiness (CallableIndexedOwnedExtendedJointReadyFamilyInputs.bridge index))
          (CallableIndexedOwnedAllocationProducer.StableOwner keys)
          (CallableIndexedOwnedExtendedJointReadyFamilyInputs.inputs wellFormed index).facts
          functions (Program.ofChecked compiled.sourceProgram) (CallableIndexedOwnedExtendedJointReadyFamilyInputs.origin index))) :
    CallableIndexedOwnedLambdaInvocationBounds.SourceContinuation (arguments := arguments) (nativeArguments := nativeArguments)
      captured code history inputs functions owner caller body budget := by
  intro entry added length copied spine kept reached child strict outcome after trace
  let index := CallableIndexedOwnedLambdaReadyFamilyReceipts.of_source_entry captured code history inputs functions owner caller body beforeTyped argumentsTyped stable
    principal observed prefixContext sourceSeed syntaxTree entry added length copied spine kept reached
  let actualEntry := CallableIndexedOwnedLambdaNestedReadyContinuations.source_admitted_entry
    captured code history inputs functions owner caller body beforeTyped argumentsTyped stable
    principal observed prefixContext sourceSeed entry added length copied spine kept reached
  have ready := below (.existing (.lambda index layouts)) child strict
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, heaps, maps, worlds,
      frame, metadata, exit, returned, related, _post⟩ :=
    CallableIndexedOwnedSourceBodyReadyBounds.preserves_at
      (CallableIndexedOwnedLambdaNestedReadyContinuations.bridge (headers := headers) owner principal)
      actualEntry.source.runtime wellFormed syntaxTree ready actualEntry trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, heaps, maps, worlds,
    frame, metadata, exit, returned.val, related⟩

include layouts wellFormed beforeTyped argumentsTyped stable observed prefixContext sourceSeed syntaxTree in
/-- The original measured prefix constructs the same static index directly;
reflection preserves the independently reconstructed Source body grade. -/
theorem native_continuation (budget : Nat)
    (below : ∀ index : CallableIndexedOwnedExtendedJointReadyFamilyInputs.Index
      (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax),
      RecursiveNamedBoundedContracts.Below budget
        (CallableRuntimeBodyReadyOrigins.ReflectsAt (CallableIndexedOwnedExtendedJointReadyFamilyInputs.protocol index)
          (readiness (CallableIndexedOwnedExtendedJointReadyFamilyInputs.bridge index))
          (CallableIndexedOwnedAllocationProducer.StableOwner keys)
          (CallableIndexedOwnedExtendedJointReadyFamilyInputs.inputs wellFormed index).facts
          functions (Program.ofChecked compiled.sourceProgram) (CallableIndexedOwnedExtendedJointReadyFamilyInputs.origin index))) :
    CallableIndexedOwnedLambdaInvocationBounds.NativeContinuation (arguments := arguments)
      captured code history inputs functions owner caller body budget := by
  intro entry reached child strict value finalStore completed
  let index := CallableIndexedOwnedLambdaReadyFamilyReceipts.of_native_entry captured code history inputs functions owner caller body beforeTyped argumentsTyped stable
    principal observed prefixContext sourceSeed syntaxTree entry reached
  let actualEntry := CallableIndexedOwnedLambdaNestedReadyContinuations.native_admitted_entry
    captured code history inputs functions owner caller body beforeTyped argumentsTyped stable
    principal observed prefixContext sourceSeed entry reached
  have ready := below (.existing (.lambda index layouts)) child strict
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, heaps, maps, worlds,
      frame, metadata, exit, returned, related, _post⟩ :=
    CallableIndexedOwnedSourceBodyReadyBounds.reflects_at
      (CallableIndexedOwnedLambdaNestedReadyContinuations.bridge (headers := headers) owner principal)
      actualEntry.source.runtime wellFormed syntaxTree ready actualEntry completed
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, heaps, maps, worlds,
    frame, metadata, exit, returned.val, related⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedExtendedJointLambdaReadyContinuations
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedExtendedJointReadyContinuations
/-! Each actual method-lambda or nested named parameter receipt embeds its
own authentic index into the extended joint family. The original pointwise
continuation proofs consume only that branch's strict body IH and retain the
same actual entries, saved caller writes and independently graded results. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedExtendedJointReadyContinuations
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open CallableIndexedOwnedAdmittedLexicalReadiness (readiness)
open CallableIndexedOwnedExtendedJointReadyFamilyInputs

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {certificates : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) →
    SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {expressionSyntax : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) → ExpressionId → Prop}
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))

/-- The existing measured family supplies this genuine dependent source IH. -/
abbrev PreservingBelow (budget : Nat) : Prop :=
  ∀ index : Index (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax),
    RecursiveNamedBoundedContracts.Below budget
      (CallableRuntimeBodyReadyOrigins.PreservesAt (protocol index) (readiness (bridge index))
        (CallableIndexedOwnedAllocationProducer.StableOwner keys) (inputs wellFormed index).facts
        functions (Program.ofChecked compiled.sourceProgram) (origin index))

/-- Native strict body grades retain each branch's independent Source result. -/
abbrev ReflectingBelow (budget : Nat) : Prop :=
  ∀ index : Index (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax),
    RecursiveNamedBoundedContracts.Below budget
      (CallableRuntimeBodyReadyOrigins.ReflectsAt (protocol index) (readiness (bridge index))
        (CallableIndexedOwnedAllocationProducer.StableOwner keys) (inputs wellFormed index).facts
        functions (Program.ofChecked compiled.sourceProgram) (origin index))

section MethodLambda
variable {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
  {mapping : LocationMap} {world : StoreTyping} {capturedActual : Environment}
  (captured : Captures compiled.indexed mapping world scope function.captured capturedActual)
  (code : Code compiled.indexed function scope captured.administrative) (history : History code)
  (support : CallableIndexedOwnedMethodLambdaSupport.Support code registry faults)
  (sourceOrigin : CallableIndexedOwnedMethodLambdaSupport.SourceOrigin support history)
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
    (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
    headers owner.key.locations 1 scope captured.canonical owner.key.frameLocation)
  (leading : captured.administrative[0]? = some support.principal.named.signature.parameterType)
  {arguments : List Dynamic.Value} {nativeArguments : List Value} {before : Dynamic.Heap} {store : Store}
  {callerScope : SourceCoreLocalCell.Scope} {callerCanonical : Environment}
  (caller : State headers keys ⟨callerScope, mapping, world, before, store, callerCanonical⟩)
  (escaped : faults .controlEscapedFunction code.compilation.internalReason)
  (beforeTyped : Dynamic.HeapWellTyped function.context before)
  (argumentsTyped : Dynamic.ValuesHaveTypes function.context before arguments support.body.types)
  (stable : CallableIndexedOwnedIndirectExpressionHeads.StableRows caller)
  (syntaxTree : GenericImperativeMatch.Syntax function.source (support.expressionSyntax function.source)
    support.body.context (.statements true function.body) function.resultType)

include observed leading sourceOrigin beforeTyped argumentsTyped stable syntaxTree wellFormed in
/-- The original actual Source entry constructs its genuine method-lambda
index and selects that exact extended-family child; no Header is introduced. -/
theorem method_lambda_source_continuation (budget : Nat)
    (below : PreservingBelow (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax) functions wellFormed budget) :
    CallableIndexedOwnedLambdaInvocationBounds.SourceContinuation (arguments := arguments) (nativeArguments := nativeArguments)
      captured code history support.body.toContext functions owner caller (support.body_origin escaped) budget := by
  exact CallableIndexedOwnedMethodLambdaReadyFamilyReceipts.source_continuation
    captured code history support sourceOrigin functions owner observed leading caller escaped
    beforeTyped argumentsTyped stable syntaxTree wellFormed budget
    (fun index => below (.methodLambda index))

include observed leading sourceOrigin beforeTyped argumentsTyped stable syntaxTree wellFormed in
/-- The measured original Prefix constructs its own exact index. The same
continuation returns the actual body pool and independent reflected grade. -/
theorem method_lambda_native_continuation (budget : Nat)
    (below : ReflectingBelow (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax) functions wellFormed budget) :
    CallableIndexedOwnedLambdaInvocationBounds.NativeContinuation (arguments := arguments)
      captured code history support.body.toContext functions owner caller (support.body_origin escaped) budget := by
  exact CallableIndexedOwnedMethodLambdaReadyFamilyReceipts.native_continuation
    captured code history support sourceOrigin functions owner observed leading caller escaped
    beforeTyped argumentsTyped stable syntaxTree wellFormed budget
    (fun index => below (.methodLambda index))
end MethodLambda

section NamedNested
variable (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  {header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
  (prefixZero : owner.key.capturePrefix = 0)
  (globals : header.globals = compiled.indexed.base.globals.length)
  (member : header ∈ headers)
  (syntaxTree : GenericImperativeMatch.Syntax header.function.source (expressionSyntax header) header.context
    (.statements true header.function.body) header.function.resultType)

include functions wellFormed prefixZero globals member syntaxTree in
/-- Actual successful named parameter receipts build the nested index from
real profile/Source admission and preserve their complete seed/bundle packet. -/
theorem named_nested_source_bodies (budget : Nat)
    (below : PreservingBelow (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax) functions wellFormed budget) :
    CallableIndexedOwnedAdmittedNamedExpressionHeads.SourceBodiesFor
      (headers := headers) (keys := keys) (owner := owner) (functions := functions)
      (registry := registry) (faults := faults) (certificates := certificates)
      (expressionSyntax := expressionSyntax) (diagnosticPolicy := .reachable) (runtime := true)
      wellFormed header budget := by
  exact CallableIndexedOwnedNamedNestedReadyFamilyReceipts.source_bodies
    (functions := functions) (owner := owner) (runtime := true)
    wellFormed prefixZero globals member syntaxTree
    (fun index => below (.namedNested index))

include functions wellFormed prefixZero globals member syntaxTree in
/-- The native callback keeps its original measured parameter prefix and
saved caller write, projecting only facets beside the same returned pool. -/
theorem named_nested_native_bodies (budget : Nat)
    (below : ReflectingBelow (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax) functions wellFormed budget) :
    CallableIndexedOwnedAdmittedNamedExpressionHeads.NativeBodiesFor
      (headers := headers) (keys := keys) (owner := owner) (functions := functions)
      (registry := registry) (faults := faults) (certificates := certificates)
      (expressionSyntax := expressionSyntax) (diagnosticPolicy := .reachable) (runtime := true)
      wellFormed header budget := by
  exact CallableIndexedOwnedNamedNestedReadyFamilyReceipts.native_bodies
    (functions := functions) (owner := owner) (runtime := true)
    wellFormed prefixZero globals member syntaxTree
    (fun index => below (.namedNested index))
end NamedNested
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedExtendedJointReadyContinuations
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredClosureInvocation
/-! Invocation starts at the actual pool after ordered arguments. The finite
association retains unrestricted ordinary or principal closure provenance,
original body Syntax and exact parameter/result compiler receipts. Captured
history and the current caller row are separate. Original payload application,
parameter allocation, strict body continuation and caller restoration retain
one actual returned pool. Legacy arbitrary-prefix selections need additional
authentic formation receipts; call-site stage/coercion gates remain separate.
No whole expression execution or completed body meaning is an input. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredClosureInvocation
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}

/-- Only full selected constructors with their genuine invocation prefixes
enter this association. Syntax belongs to exactly the retained same-Code body. -/
inductive Association (headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram)))
    (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (mapping : LocationMap) (world : StoreTyping) :
    Dynamic.Closure → Value → List CallableIndexedParameterCertificates.Binding → Ty → Ty → Prop where
  | ordinary {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {actual : Environment}
      (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
      (captured : Captures compiled.indexed mapping world scope function.captured actual)
      (code : Code compiled.indexed function scope captured.administrative) (history : History code)
      (support : CallableIndexedOwnedOrdinaryLambdaSupport.Support code registry faults)
      (sourceOrigin : CallableIndexedOwnedOrdinaryLambdaSupport.SourceOrigin support history)
      (prefixContext : captured.administrative = RecursiveNamedLambdaFormationHeads.nativePrefix
        (values := .initial compiled.compatible.checked) support.caller)
      (observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
        (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
        headers owner.key.locations 1 scope captured.canonical owner.key.frameLocation)
      (referenceIndex : code.referenceIndex = scope.length + 1 + compiled.indexed.base.globals.length)
      (typed : RuntimeValueHasType world (value code captured.embedding history.native actual)
        (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore) compiled.indexed.layouts.definitions)
      (escaped : faults .controlEscapedFunction code.compilation.internalReason)
      (syntaxTree : GenericImperativeMatch.Syntax function.source (support.expressionSyntax function.source)
        support.body.context (.statements true function.body) function.resultType) :
      Association headers keys registry faults mapping world function
        (value code captured.embedding history.native actual) code.receipt.loweredParameters
        code.receipt.parameterCore code.receipt.resultCore
  | principal {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {actual : Environment}
      (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
      (captured : Captures compiled.indexed mapping world scope function.captured actual)
      (code : Code compiled.indexed function scope captured.administrative) (history : History code)
      (support : CallableIndexedOwnedMethodLambdaSupport.Support code registry faults)
      (sourceOrigin : CallableIndexedOwnedMethodLambdaSupport.SourceOrigin support history)
      (observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
        (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
        headers owner.key.locations 1 scope captured.canonical owner.key.frameLocation)
      (leading : captured.administrative[0]? = some support.principal.named.signature.parameterType)
      (referenceIndex : code.referenceIndex = scope.length + 1 + compiled.indexed.base.globals.length)
      (typed : RuntimeValueHasType world (value code captured.embedding history.native actual)
        (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore) compiled.indexed.layouts.definitions)
      (escaped : faults .controlEscapedFunction code.compilation.internalReason)
      (syntaxTree : GenericImperativeMatch.Syntax function.source (support.expressionSyntax function.source)
        support.body.context (.statements true function.body) function.resultType) :
      Association headers keys registry faults mapping world function
        (value code captured.embedding history.native actual) code.receipt.loweredParameters
        code.receipt.parameterCore code.receipt.resultCore

/-- The complete association reconstructs the exact same selected payload;
there is no inverse function-model inclusion or weaker representation. -/
theorem Association.selection {mapping : LocationMap} {world : StoreTyping}
    {function : Dynamic.Closure} {native : Value} {bindings : List CallableIndexedParameterCertificates.Binding}
    {parameterCore resultCore : Ty}
    (association : Association headers keys registry faults mapping world function native bindings parameterCore resultCore) :
    CallableIndexedOwnedGeneralFunctionSelection.Selection headers keys registry faults mapping world
      (FunctionValues.sourceType function) (.closure function) native
      (CallableContract.functionType parameterCore resultCore) := by
  cases association with
  | ordinary owner captured code history support sourceOrigin prefixContext observed referenceIndex typed _escaped _syntax =>
    exact .ordinary_lambda owner captured code history support sourceOrigin prefixContext observed referenceIndex typed
  | principal owner captured code history support sourceOrigin observed leading referenceIndex typed _escaped _syntax =>
    exact .principal_lambda owner captured code history support sourceOrigin observed leading referenceIndex typed

variable (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))

/-- Every semantic/effect field and stable row describes the actual reached
pool returned by the original invocation, including fault outcomes. -/
def ResultAt {index : ProtectedStateTransition.Index} (initial : State headers keys index)
    (function : Dynamic.Closure) (resultCore : Ty) (outcome : Dynamic.ExpressionOutcome)
    (after : Dynamic.Heap) (value : Value) (finalStore : Store) : Prop :=
  ∃ finalMap finalWorld,
    FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      finalMap finalWorld function.resultType resultCore faults outcome value ∧
    CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
    LocationMap.Extends index.mapping finalMap ∧ WorldExtends index.world finalWorld ∧
    AdministrativePreserved index.mapping index.store finalMap finalStore ∧ Dynamic.HeapMetadataExtend index.heap after ∧
    ∃ reached : State headers keys (index.extend finalMap finalWorld after finalStore),
      Relates initial reached ∧ StableRows reached

section Invocation
variable {certificates : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) →
    SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {expressionSyntax : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) → ExpressionId → Prop}
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {callerScope : SourceCoreLocalCell.Scope} {callerCanonical : Environment}
  {function : Dynamic.Closure} {native : Value} {bindings : List CallableIndexedParameterCertificates.Binding}
  {parameterCore resultCore : Ty}
  (association : Association headers keys registry faults mapping world function native bindings parameterCore resultCore)
  (initial : State headers keys ⟨callerScope, mapping, world, before, store, callerCanonical⟩)
  {arguments : List Dynamic.Value} {nativeArguments : List Value}
  (represented : CallableIndexedParameterMeaning.Arguments
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
    mapping world bindings arguments nativeArguments)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions mapping world before store)
  (beforeTyped : Dynamic.HeapWellTyped function.context before)
  (argumentsTyped : Dynamic.ValuesHaveTypes function.context before arguments
    (function.parameters.map (fun binding => binding.scheme.body)))
  (locals : Dynamic.EnvironmentAgrees before function.context.locals function.captured)
  (stable : StableRows initial)

include wellFormed association represented heaps beforeTyped argumentsTyped locals stable in
/-- Actual raw arguments and current row admission select the original
parameter entry and strict shared-family body IH. The saved caller is current. -/
theorem preserves_at (budget : Nat)
    (below : CallableIndexedOwnedExtendedJointReadyContinuations.PreservingBelow
      (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax) functions wellFormed budget)
    {size : Nat} {callContext : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.CallOutcome (Program.ofChecked compiled.sourceProgram)
      size callContext callerEvidence function.evidence before (.closure function) arguments outcome after)
    (within : size ≤ budget) :
    ∃ value finalStore,
      Evaluates [native, DataPatternValues.packValues nativeArguments] store
        CallableIndexedLambdaCalls.applyPayload value finalStore ∧
      ResultAt (registry := registry) (faults := faults) functions initial function resultCore outcome after value finalStore := by
  cases association with
  | ordinary owner captured code history support sourceOrigin prefixContext observed referenceIndex _typed escaped syntaxTree =>
    have raw : Dynamic.ValuesHaveTypes function.context before arguments support.body.types := by
      simpa only [Dynamic.MonoBindersExtend.bodyTypes_eq support.body.extended] using argumentsTyped
    obtain ⟨currentMetadata, currentCarried⟩ := stable owner.position
    have reference : captured.canonical[code.referenceIndex]? =
        some (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation) := by
      rw [referenceIndex]
      exact observed.reference
    have meaning := CallableIndexedOwnedExtendedJointLambdaReadyContinuations.source_continuation
      (nativeArguments := nativeArguments) captured code history support.body.toContext functions owner initial
      (support.body_origin escaped) beforeTyped raw stable support.caller observed prefixContext
      sourceOrigin.metadata syntaxTree wellFormed rfl budget below
    obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, result, finalHeaps, maps, worlds, frame, metadata, reached, related⟩ :=
      CallableIndexedOwnedLambdaInvocationBounds.application_preserves_bounded_at
        captured code history support.body.toContext functions represented owner initial heaps locals
        reference currentCarried (CallableIndexedLambdaTemplatePermission.lambda_allowed code history)
        (support.body_origin escaped) budget meaning trace within
    exact ⟨value, finalStore, evaluated, finalMap, finalWorld, result, finalHeaps, maps, worlds,
      frame, metadata, reached, related, StableRows.after_administrative initial reached stable frame⟩
  | principal owner captured code history support sourceOrigin observed leading referenceIndex _typed escaped syntaxTree =>
    have raw : Dynamic.ValuesHaveTypes function.context before arguments support.body.types := by
      simpa only [Dynamic.MonoBindersExtend.bodyTypes_eq support.body.extended] using argumentsTyped
    obtain ⟨currentMetadata, currentCarried⟩ := stable owner.position
    have reference : captured.canonical[code.referenceIndex]? =
        some (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation) := by
      rw [referenceIndex]
      exact observed.reference
    have meaning := CallableIndexedOwnedExtendedJointReadyContinuations.method_lambda_source_continuation
      (nativeArguments := nativeArguments) functions wellFormed captured code history support sourceOrigin owner
      observed leading initial escaped beforeTyped raw stable syntaxTree budget below
    obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, result, finalHeaps, maps, worlds, frame, metadata, reached, related⟩ :=
      CallableIndexedOwnedLambdaInvocationBounds.application_preserves_bounded_at
        captured code history support.body.toContext functions represented owner initial heaps locals
        reference currentCarried (CallableIndexedLambdaTemplatePermission.lambda_allowed code history)
        (support.body_origin escaped) budget meaning trace within
    exact ⟨value, finalStore, evaluated, finalMap, finalWorld, result, finalHeaps, maps, worlds,
      frame, metadata, reached, related, StableRows.after_administrative initial reached stable frame⟩

include wellFormed association represented heaps beforeTyped argumentsTyped locals stable in
/-- The original measured payload prefix keeps its strict body bound and
reconstructs an independently sized Source call at the same returned pool. -/
theorem reflects_at (budget : Nat)
    (below : CallableIndexedOwnedExtendedJointReadyContinuations.ReflectingBelow
      (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax) functions wellFormed budget)
    {size : Nat} {callContext : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    {value : Value} {finalStore : Store}
    (completed : EvaluationSize size [native, DataPatternValues.packValues nativeArguments] store
      CallableIndexedLambdaCalls.applyPayload value finalStore)
    (within : size ≤ budget) :
    ∃ sourceSize outcome after,
      RecursiveNamedCallBounds.CallOutcome (Program.ofChecked compiled.sourceProgram)
        sourceSize callContext callerEvidence function.evidence before (.closure function) arguments outcome after ∧
      ResultAt (registry := registry) (faults := faults) functions initial function resultCore outcome after value finalStore := by
  cases association with
  | ordinary owner captured code history support sourceOrigin prefixContext observed referenceIndex _typed escaped syntaxTree =>
    have raw : Dynamic.ValuesHaveTypes function.context before arguments support.body.types := by
      simpa only [Dynamic.MonoBindersExtend.bodyTypes_eq support.body.extended] using argumentsTyped
    obtain ⟨currentMetadata, currentCarried⟩ := stable owner.position
    have reference : captured.canonical[code.referenceIndex]? =
        some (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation) := by
      rw [referenceIndex]
      exact observed.reference
    have meaning := CallableIndexedOwnedExtendedJointLambdaReadyContinuations.native_continuation
      captured code history support.body.toContext functions owner initial
      (support.body_origin escaped) beforeTyped raw stable support.caller observed prefixContext
      sourceOrigin.metadata syntaxTree wellFormed rfl budget below
    obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, result, finalHeaps, maps, worlds, frame, metadata, reached, related⟩ :=
      CallableIndexedOwnedLambdaInvocationBounds.application_reflects_bounded_at
        captured code history support.body.toContext functions represented owner initial heaps locals
        reference currentCarried (CallableIndexedLambdaTemplatePermission.lambda_allowed code history)
        (support.body_origin escaped) budget meaning completed within
    exact ⟨sourceSize, outcome, after, trace, finalMap, finalWorld, result, finalHeaps, maps, worlds,
      frame, metadata, reached, related, StableRows.after_administrative initial reached stable frame⟩
  | principal owner captured code history support sourceOrigin observed leading referenceIndex _typed escaped syntaxTree =>
    have raw : Dynamic.ValuesHaveTypes function.context before arguments support.body.types := by
      simpa only [Dynamic.MonoBindersExtend.bodyTypes_eq support.body.extended] using argumentsTyped
    obtain ⟨currentMetadata, currentCarried⟩ := stable owner.position
    have reference : captured.canonical[code.referenceIndex]? =
        some (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation) := by
      rw [referenceIndex]
      exact observed.reference
    have meaning := CallableIndexedOwnedExtendedJointReadyContinuations.method_lambda_native_continuation
      functions wellFormed captured code history support sourceOrigin owner observed leading initial escaped
      beforeTyped raw stable syntaxTree budget below
    obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, result, finalHeaps, maps, worlds, frame, metadata, reached, related⟩ :=
      CallableIndexedOwnedLambdaInvocationBounds.application_reflects_bounded_at
        captured code history support.body.toContext functions represented owner initial heaps locals
        reference currentCarried (CallableIndexedLambdaTemplatePermission.lambda_allowed code history)
        (support.body_origin escaped) budget meaning completed within
    exact ⟨sourceSize, outcome, after, trace, finalMap, finalWorld, result, finalHeaps, maps, worlds,
      frame, metadata, reached, related, StableRows.after_administrative initial reached stable frame⟩

end Invocation

section Caller
variable {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  {slots : ProtectedStateTransition.Index → Prop}
  (carrier : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) slots callerProtocol)

/-- Repacking exposes both the exact invocation pool and the returned caller
whose pool equals it. Every original semantic and effect receipt is retained. -/
def CallerResultAt {index : ProtectedStateTransition.Index} (initial : callerProtocol.State index)
    (function : Dynamic.Closure) (resultCore : Ty) (outcome : Dynamic.ExpressionOutcome)
    (after : Dynamic.Heap) (value : Value) (finalStore : Store) : Prop :=
  ∃ finalMap finalWorld,
    FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      finalMap finalWorld function.resultType resultCore faults outcome value ∧
    CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
    LocationMap.Extends index.mapping finalMap ∧ WorldExtends index.world finalWorld ∧
    AdministrativePreserved index.mapping index.store finalMap finalStore ∧ Dynamic.HeapMetadataExtend index.heap after ∧
    ∃ reached : State headers keys (index.extend finalMap finalWorld after finalStore),
      Relates (carrier.pool initial) reached ∧ StableRows reached ∧
      ∃ returned : callerProtocol.State (index.extend finalMap finalWorld after finalStore),
        carrier.pool returned = reached ∧ callerProtocol.Relates initial returned

/-- The real invocation effects authorize restoration of the original caller
around exactly the same reached pool. No canonical slots are inferred. -/
theorem ResultAt.restore {index : ProtectedStateTransition.Index} (initial : callerProtocol.State index)
    {function : Dynamic.Closure} {resultCore : Ty} {outcome : Dynamic.ExpressionOutcome}
    {after : Dynamic.Heap} {value : Value} {finalStore : Store}
    (result : ResultAt (registry := registry) (faults := faults) functions
      (carrier.pool initial) function resultCore outcome after value finalStore) :
    CallerResultAt (registry := registry) (faults := faults) functions carrier initial
      function resultCore outcome after value finalStore := by
  obtain ⟨finalMap, finalWorld, represented, heaps, maps, worlds, frame, metadata, reached, related, stable⟩ := result
  obtain ⟨returned, samePool, callerRelated⟩ := carrier.restore initial reached maps worlds frame metadata related
  exact ⟨finalMap, finalWorld, represented, heaps, maps, worlds, frame, metadata,
    reached, related, stable, returned, samePool, callerRelated⟩

variable {certificates : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) →
    SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {expressionSyntax : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) → ExpressionId → Prop}
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {callerScope : SourceCoreLocalCell.Scope} {callerCanonical : Environment}
  {function : Dynamic.Closure} {native : Value} {bindings : List CallableIndexedParameterCertificates.Binding}
  {parameterCore resultCore : Ty}
  (association : Association headers keys registry faults mapping world function native bindings parameterCore resultCore)
  (initial : callerProtocol.State ⟨callerScope, mapping, world, before, store, callerCanonical⟩)
  {arguments : List Dynamic.Value} {nativeArguments : List Value}
  (represented : CallableIndexedParameterMeaning.Arguments
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
    mapping world bindings arguments nativeArguments)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions mapping world before store)
  (beforeTyped : Dynamic.HeapWellTyped function.context before)
  (argumentsTyped : Dynamic.ValuesHaveTypes function.context before arguments
    (function.parameters.map (fun binding => binding.scheme.body)))
  (locals : Dynamic.EnvironmentAgrees before function.context.locals function.captured)
  (stable : StableRows (carrier.pool initial))

include wellFormed association represented heaps beforeTyped argumentsTyped locals stable in
/-- The stronger actual caller is returned using the same complete original
application result, current saved frame and actual administrative receipts. -/
theorem preserves_for (budget : Nat)
    (below : CallableIndexedOwnedExtendedJointReadyContinuations.PreservingBelow
      (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax) functions wellFormed budget)
    {size : Nat} {callContext : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.CallOutcome (Program.ofChecked compiled.sourceProgram)
      size callContext callerEvidence function.evidence before (.closure function) arguments outcome after)
    (within : size ≤ budget) :
    ∃ value finalStore,
      Evaluates [native, DataPatternValues.packValues nativeArguments] store
        CallableIndexedLambdaCalls.applyPayload value finalStore ∧
      CallerResultAt (registry := registry) (faults := faults) functions carrier initial
        function resultCore outcome after value finalStore := by
  obtain ⟨value, finalStore, evaluated, result⟩ := preserves_at functions wellFormed association
    (carrier.pool initial) represented heaps beforeTyped argumentsTyped locals stable budget below trace within
  exact ⟨value, finalStore, evaluated, result.restore functions carrier initial⟩

include wellFormed association represented heaps beforeTyped argumentsTyped locals stable in
/-- Native reflection restores that same actual caller and retains the
independently reconstructed Source call, without comparing the two grades. -/
theorem reflects_for (budget : Nat)
    (below : CallableIndexedOwnedExtendedJointReadyContinuations.ReflectingBelow
      (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax) functions wellFormed budget)
    {size : Nat} {callContext : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    {value : Value} {finalStore : Store}
    (completed : EvaluationSize size [native, DataPatternValues.packValues nativeArguments] store
      CallableIndexedLambdaCalls.applyPayload value finalStore)
    (within : size ≤ budget) :
    ∃ sourceSize outcome after,
      RecursiveNamedCallBounds.CallOutcome (Program.ofChecked compiled.sourceProgram)
        sourceSize callContext callerEvidence function.evidence before (.closure function) arguments outcome after ∧
      CallerResultAt (registry := registry) (faults := faults) functions carrier initial
        function resultCore outcome after value finalStore := by
  obtain ⟨sourceSize, outcome, after, trace, result⟩ := reflects_at functions wellFormed association
    (carrier.pool initial) represented heaps beforeTyped argumentsTyped locals stable budget below completed within
  exact ⟨sourceSize, outcome, after, trace, result.restore functions carrier initial⟩
end Caller
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredClosureInvocation
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredClosureSourceArguments
/-! Independent raw Source argument typing is transported at the actual
argument post into the selected closure context. The original packed-value and
arity rules recover the real Source binder row. Native parameter vectors do
not supply Source types or deep heap admission. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredClosureSourceArguments
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission

/-- All facts refer to the same actual after-argument Source heap. Captured
locals are checked there, independently of immutable compiler history. -/
structure SourceArguments (function : Dynamic.Closure) (heap : Dynamic.Heap)
    (arguments : List Dynamic.Value) : Prop where
  heaps : Dynamic.HeapWellTyped function.context heap
  arguments : Dynamic.ValuesHaveTypes function.context heap arguments
    (function.parameters.map (fun binder => binder.scheme.body))
  captures : Dynamic.EnvironmentAgrees heap function.context.locals function.captured
  code : Dynamic.ClosureCodeValid function.context function
  covers : function.evidence.Covers function.context

variable {program : Program} {context : SourceSemantics.Context} {source : TypedSource}
  {function : Dynamic.Closure} {heap : Dynamic.Heap}
  {parameter result : TypeSystem.Ty} {arguments : List Dynamic.Value}
  {types : List TypeSystem.Ty} {packed : Dynamic.Value}

/-- Actual Source callee typing fixes its exact binder bundle. Genuine packed
argument typing and matching actual arity then recover its raw parameter row.
Closed-context transport keeps this heap and these values unchanged. -/
theorem at_arguments (runtime : Dynamic.SourceRuntimeValid program context source)
    (calleeTyped : Dynamic.ValueHasType context heap (.closure function) (.function parameter result))
    (heapTyped : Dynamic.HeapWellTyped context heap)
    (argumentsTyped : Dynamic.ValuesHaveTypes context heap arguments types)
    (packing : Dynamic.ValuesPack arguments packed)
    (bundle : TypeSystem.Ty.productMany types = parameter)
    (arity : arguments.length = function.parameters.length) : SourceArguments function heap arguments := by
  obtain ⟨parameters, _result, signatures, code, covers, captures⟩ := calleeTyped.closure_function_inv
  have packedTyped : Dynamic.ValueHasType context heap packed
      (TypeSystem.Ty.productMany (function.parameters.map (fun binder => binder.scheme.body))) := by
    rw [← parameters, ← bundle]
    exact packing.hasType argumentsTyped
  have closureHeap := heapTyped.transportClosed signatures runtime.closed code.closed
    runtime.variables_closed code.residual_variables_open
  have closurePacked := packedTyped.transportClosed signatures runtime.closed code.closed
    runtime.variables_closed code.residual_variables_open
  have closureArguments := packing.unpackTypes closurePacked (by simpa using arity)
  exact ⟨closureHeap, closureArguments, captures, code, covers⟩

universe u
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
    (fun _ => True) callerProtocol)
  {index : ProtectedStateTransition.Index} (reached : callerProtocol.State index)

/-- The genuine admitted after-argument state supplies both deep Source heap
validity and every current owned row. Neither is replaced by a captured row or
an earlier callee state. The arity/bundle remain authentic Source call facts. -/
theorem at_admitted_arguments (runtime : Dynamic.SourceRuntimeValid program context source)
    (admitted : Admission bridge context reached)
    (calleeTyped : Dynamic.ValueHasType context index.heap (.closure function) (.function parameter result))
    (argumentsTyped : Dynamic.ValuesHaveTypes context index.heap arguments types)
    (packing : Dynamic.ValuesPack arguments packed)
    (bundle : TypeSystem.Ty.productMany types = parameter)
    (arity : arguments.length = function.parameters.length) :
    SourceArguments function index.heap arguments ∧
    CallableIndexedOwnedIndirectExpressionHeads.StableRows (bridge.pool reached) :=
  ⟨at_arguments runtime calleeTyped admitted.heap argumentsTyped packing bundle arity, admitted.rows⟩

/-- The actual argument trace's Source type extension carries callee typing
from its own success post to the later argument post. All deep heap and owned
row admission is still taken from the actual later state. -/
theorem after_argument_extension {calleeHeap : Dynamic.Heap}
    (runtime : Dynamic.SourceRuntimeValid program context source)
    (admitted : Admission bridge context reached)
    (calleeTyped : Dynamic.ValueHasType context calleeHeap (.closure function) (.function parameter result))
    (extension : Dynamic.HeapTypesExtend calleeHeap index.heap)
    (argumentsTyped : Dynamic.ValuesHaveTypes context index.heap arguments types)
    (packing : Dynamic.ValuesPack arguments packed)
    (bundle : TypeSystem.Ty.productMany types = parameter)
    (arity : arguments.length = function.parameters.length) :
    SourceArguments function index.heap arguments ∧
    CallableIndexedOwnedIndirectExpressionHeads.StableRows (bridge.pool reached) :=
  at_admitted_arguments bridge reached runtime admitted (calleeTyped.mono extension)
    argumentsTyped packing bundle arity

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredClosureSourceArguments
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredClosureArgumentReceipts
/-! Original indirect-call Source typing and the actual successful ordered
argument trace retain independent raw types and true Source heap extension.
The empty argument-coercion specialization uses the original valid path.
Arity comes from the selected closure's genuine binder representation.
Current owned rows and later admission remain separate actual-state receipts;
native reflection must first obtain its real Source argument trace. Body
Syntax, compiler pack alignment, stage gates and nonempty coercions remain
separate static and semantic cuts. No execution law is an input. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredClosureArgumentReceipts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof

/-- One authentic parent inversion retains both the callee and the original
ordered raw argument row, including the original application certificate. -/
theorem original_facts {source : TypedSource} {context : SourceSemantics.Context}
    {root callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
    {node : ExpressionNode} {type : TypeSystem.Ty}
    (unique : NodeOccurrencesUnique source)
    (found : source.lookupExpression? root = some node)
    (form : node.form = .call callee ids (.indirect metadata))
    (typed : ExpressionHasType source context root type) :
    ∃ parameter result types,
      ExpressionHasType source context callee (.function parameter result) ∧
      ExpressionsHaveTypes source context ids types ∧
      IndirectApplicationValid context metadata types parameter := by
  cases typed with
  | @intro _ _ actualNode rawType plan contains raw _ _ _ _ =>
    have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
    subst actualNode
    rw [form] at raw
    cases raw with
    | indirectCall calleeTyped argumentsTyped application =>
      exact ⟨_, _, _, calleeTyped, argumentsTyped, application⟩

/-- Empty coercions identify the real Source bundle through the valid path;
no native parameter vector or packed-type injectivity is used. -/
theorem empty_bundle {context : SourceSemantics.Context} {metadata : IndirectCallResolution}
    {types : List TypeSystem.Ty} {parameter : TypeSystem.Ty}
    (application : IndirectApplicationValid context metadata types parameter)
    (empty : metadata.argumentCoercions = []) :
    TypeSystem.Ty.productMany types = parameter := by
  cases application with
  | intro _ before _ path =>
    have endpoint := path.foldl_target
    rw [empty, List.foldl_nil] at endpoint
    exact before.symm.trans endpoint

/-- The same actual Source trace supplies raw values, deep heap typing and
true heap-type extension. The packed value is constructed from those values. -/
theorem after_trace {program : Program} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {ids : List ExpressionId} {types : List TypeSystem.Ty}
    {size : Nat} {arguments : List Dynamic.Value}
    (wellFormed : ProgramWellFormed program)
    (runtime : Dynamic.SourceRuntimeValid program context source)
    (covers : evidence.Covers context)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (heapTyped : Dynamic.HeapWellTyped context before)
    (typed : ExpressionsHaveTypes source context ids types)
    (trace : SourceExecutionSize.ExpressionsEvaluate program size context evidence source environment
      before ids arguments after) :
    ∃ packed, Dynamic.ValuesPack arguments packed ∧
      Dynamic.ValuesHaveTypes context after arguments types ∧
      Dynamic.HeapWellTyped context after ∧ Dynamic.HeapTypesExtend before after ∧
      Dynamic.ValueHasType context after packed (TypeSystem.Ty.productMany types) := by
  have preserves : Dynamic.ExpressionExecutionPreserves program context evidence source environment := by
    intro before after id value type covers locals heapTyped typed evaluated
    exact wellFormed.wholeLanguagePreservation.expression context evidence source environment
      before after id value type runtime covers locals heapTyped typed evaluated
  obtain ⟨valuesTyped, reachedTyped, extension⟩ :=
    Dynamic.ExpressionsEvaluate.preserves preserves covers locals heapTyped typed trace.sound
  obtain ⟨packed, packing⟩ := Dynamic.ValuesPack.exists_pack arguments
  exact ⟨packed, packing, valuesTyped, reachedTyped, extension, packing.hasType valuesTyped⟩

/-- Actual selected binder representation fixes arity independently of the
Source bundle equation. Both constructors retain the real Code receipt. -/
theorem arity_of_association {compiled : SourceCoreUnifiedCompilation.Compiled}
    {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
    {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    {mapping : LocationMap} {world : StoreTyping} {function : Dynamic.Closure} {native : Value}
    {bindings : List CallableIndexedParameterCertificates.Binding} {parameterCore resultCore : Ty}
    {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {nativeDefinitions : DataEnvironment}
    {model : GenericHeap.PayloadModel catalog projects nativeDefinitions}
    {arguments : List Dynamic.Value} {nativeArguments : List Value}
    (association : CallableIndexedOwnedStoredClosureInvocation.Association
      headers keys registry faults mapping world function native bindings parameterCore resultCore)
    (represented : CallableIndexedParameterMeaning.Arguments model mapping world bindings arguments nativeArguments) :
    arguments.length = function.parameters.length := by
  cases association with
  | ordinary _ _ code _ _ _ _ _ _ _ _ _ =>
    rw [CallableIndexedLambdaEntryPrefix.parameters (values := .initial compiled.compatible.checked) code,
      List.length_map]
    exact represented.length.1.symm
  | principal _ _ code _ _ _ _ _ _ _ _ _ =>
    rw [CallableIndexedLambdaEntryPrefix.parameters (values := .initial compiled.compatible.checked) code,
      List.length_map]
    exact represented.length.1.symm

/-- Genuine callee typing is carried along the actual argument extension,
then the original closed-context transport derives raw closure inputs at that
same heap. Current owned rows are supplied by the later admitted state. -/
theorem closure_after_trace {program : Program} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {ids : List ExpressionId} {types : List TypeSystem.Ty}
    {size : Nat} {arguments : List Dynamic.Value} {function : Dynamic.Closure}
    {parameter result : TypeSystem.Ty} {metadata : IndirectCallResolution}
    (wellFormed : ProgramWellFormed program)
    (runtime : Dynamic.SourceRuntimeValid program context source)
    (covers : evidence.Covers context)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (heapTyped : Dynamic.HeapWellTyped context before)
    (typed : ExpressionsHaveTypes source context ids types)
    (application : IndirectApplicationValid context metadata types parameter)
    (empty : metadata.argumentCoercions = [])
    (calleeTyped : Dynamic.ValueHasType context before (.closure function) (.function parameter result))
    (arity : arguments.length = function.parameters.length)
    (trace : SourceExecutionSize.ExpressionsEvaluate program size context evidence source environment
      before ids arguments after) :
    CallableIndexedOwnedStoredClosureSourceArguments.SourceArguments function after arguments ∧
      Dynamic.HeapTypesExtend before after := by
  obtain ⟨packed, packing, valuesTyped, reachedTyped, extension, _⟩ :=
    after_trace wellFormed runtime covers locals heapTyped typed trace
  exact ⟨CallableIndexedOwnedStoredClosureSourceArguments.at_arguments runtime
    (calleeTyped.mono extension) reachedTyped valuesTyped packing (empty_bundle application empty) arity,
    extension⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredClosureArgumentReceipts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredArgumentAlignment
/-! Static argument alignment keeps the raw Source and native type rows
independent. The conventional zero and singleton packings require a genuine
equal-length receipt before their packed types determine an ordered row.
Actual represented values and authentic binder arity supply those lengths;
no count is inferred from a type or from a native representation. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredArgumentAlignment
open Core Frontend SourceInference GeneralHeap

/-- Source packed products determine their ordered row only at equal lengths. -/
theorem source_rows_of_bundle {left right : List TypeSystem.Ty}
    (lengths : left.length = right.length)
    (packed : TypeSystem.Ty.productMany left = TypeSystem.Ty.productMany right) : left = right := by
  induction left generalizing right with
  | nil => cases right <;> simp_all
  | cons head tail ih =>
    cases right with
    | nil => simp at lengths
    | cons other rest =>
      have tailLengths : tail.length = rest.length := Nat.succ.inj lengths
      cases tail with
      | nil =>
        cases rest with
        | nil => simpa only [TypeSystem.Ty.productMany, List.cons.injEq, and_true] using packed
        | cons => simp at tailLengths
      | cons next more =>
        cases rest with
        | nil => simp at tailLengths
        | cons nextOther restMore =>
          simp only [TypeSystem.Ty.productMany, TypeSystem.Ty.product.injEq] at packed
          rw [packed.1, ih tailLengths packed.2]

/-- Native packed products retain the same independent physical count. -/
theorem native_rows_of_bundle {left right : List Ty}
    (lengths : left.length = right.length)
    (packed : SourceCoreCompatibleCatalog.packTypes left = SourceCoreCompatibleCatalog.packTypes right) :
    left = right := by
  induction left generalizing right with
  | nil => cases right <;> simp_all
  | cons head tail ih =>
    cases right with
    | nil => simp at lengths
    | cons other rest =>
      have tailLengths : tail.length = rest.length := Nat.succ.inj lengths
      cases tail with
      | nil =>
        cases rest with
        | nil => simpa only [SourceCoreCompatibleCatalog.packTypes, List.cons.injEq, and_true] using packed
        | cons => simp at tailLengths
      | cons next more =>
        cases rest with
        | nil => simp at tailLengths
        | cons nextOther restMore =>
          simp only [SourceCoreCompatibleCatalog.packTypes, Ty.product.injEq] at packed
          rw [packed.1, ih tailLengths packed.2]

variable {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  {definitions : DataEnvironment} {model : GenericHeap.PayloadModel catalog projects definitions}
  {mapping : LocationMap} {world : StoreTyping}
  {sourceTypes : List TypeSystem.Ty} {types : List Ty}
  {sources : List Dynamic.Value} {values : List Value}

/-- The genuine raw row has one entry for each actually represented Source value. -/
theorem source_length
    (represented : DataExpressionSequence.Values model mapping world sourceTypes types sources values) :
    sourceTypes.length = sources.length := by
  induction represented with
  | nil => rfl
  | cons _ _ ih => exact congrArg Nat.succ ih

/-- Exact independent raw and native rows construct the original binder
representation without changing any represented value or its order. -/
theorem arguments_of_rows (bindings : List CallableIndexedParameterCertificates.Binding)
    (represented : DataExpressionSequence.Values model mapping world sourceTypes types sources values)
    (sourceRow : sourceTypes = bindings.map (fun binding => binding.1.scheme.body))
    (nativeRow : types = bindings.map Prod.snd) :
    CallableIndexedParameterMeaning.Arguments model mapping world bindings sources values := by
  subst sourceTypes
  subst types
  induction bindings generalizing sources values with
  | nil => cases represented; exact .nil
  | cons binding tail ih =>
    cases represented with
    | cons head rest => exact .cons head (ih rest)

/-- Actual represented values, genuine selected binder arity and the two
independent packed-type receipts close the original binder argument vector. -/
theorem arguments_of_bundles (bindings : List CallableIndexedParameterCertificates.Binding)
    (represented : DataExpressionSequence.Values model mapping world sourceTypes types sources values)
    (arity : sources.length = bindings.length)
    (sourceBundle : TypeSystem.Ty.productMany sourceTypes =
      TypeSystem.Ty.productMany (bindings.map (fun binding => binding.1.scheme.body)))
    (nativeBundle : SourceCoreCompatibleCatalog.packTypes types =
      SourceCoreCompatibleCatalog.packTypes (bindings.map Prod.snd)) :
    CallableIndexedParameterMeaning.Arguments model mapping world bindings sources values := by
  have rawLength : sourceTypes.length = (bindings.map (fun binding => binding.1.scheme.body)).length := by
    simpa only [List.length_map] using (source_length represented).trans arity
  have nativeLength : types.length = (bindings.map Prod.snd).length := by
    simpa only [List.length_map] using represented.length.1.trans arity
  exact arguments_of_rows bindings represented
    (source_rows_of_bundle rawLength sourceBundle) (native_rows_of_bundle nativeLength nativeBundle)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredArgumentAlignment
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredNativePackReceipts
/-! The actual successful callee representation and complete selected Code
identify only native callable parameter/result types. Authentic independent
binder projections then identify that same Code's packed binder type. An
arbitrary callable or binder policy supplies neither projection law. Original
raw Source bundles, genuine counts, body Syntax and stage gates stay separate. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredNativePackReceipts
open Core Frontend SourceInference GeneralHeap CompatiblePayload CallableIndexedLambdaValues

/-- The original native callable wrapper retains both type parameters. -/
theorem callable_parameters {leftParameter leftResult rightParameter rightResult : Ty}
    (same : CallableContract.functionType leftParameter leftResult =
      CallableContract.functionType rightParameter rightResult) :
    leftParameter = rightParameter ∧ leftResult = rightResult := by
  have tagged := (Ty.product.inj same).1
  have function := (Ty.product.inj tagged).2
  have parameters := Ty.function.inj function
  exact ⟨parameters.1, (Ty.sum.inj parameters.2).2⟩

/-- Each genuine binder projection keeps the original ordered packed product.
This is a static list proof; no projection is recovered from a native value. -/
theorem binding_projection_pack {checked : SourceCoreCompatibleCatalog.Checked}
    (bindings : List CallableIndexedParameterCertificates.Binding)
    (projected : ∀ binding ∈ bindings,
      checked.catalog.project binding.1.scheme.body = .ok binding.2) :
    checked.catalog.project (TypeSystem.Ty.productMany (bindings.map (fun binding => binding.1.scheme.body))) =
      .ok (SourceCoreCompatibleCatalog.packTypes (bindings.map Prod.snd)) := by
  induction bindings with
  | nil => rfl
  | cons binding rest ih =>
    have head := projected binding (by simp)
    cases rest with
    | nil => exact head
    | cons next tail =>
      have remainder := ih (fun item member => projected item (List.mem_cons_of_mem _ member))
      change (do pure (Ty.product (← checked.catalog.project binding.1.scheme.body)
        (← checked.catalog.project (TypeSystem.Ty.productMany ((next :: tail).map
          (fun binding : CallableIndexedParameterCertificates.Binding => binding.1.scheme.body)))))) = _
      rw [head, remainder]
      rfl

/-- The complete Code's actual Source signature and real binder row fix its
native bundle when both independent canonical projections are retained. -/
theorem code_binding_pack {checked : SourceCoreCompatibleCatalog.Checked}
    {prepared : SourceCoreCallableIndexedPrograms.Prepared checked}
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    (code : Code prepared function scope administrative)
    (profile : checked.catalog.callableContracts = true)
    (projected : ∀ binding ∈ code.receipt.loweredParameters,
      checked.catalog.project binding.1.scheme.body = .ok binding.2)
    (resultProjected : checked.catalog.project function.resultType = .ok code.receipt.resultCore) :
    code.receipt.parameterCore = SourceCoreCompatibleCatalog.packTypes (code.receipt.loweredParameters.map Prod.snd) := by
  have packed := binding_projection_pack code.receipt.loweredParameters projected
  have parameters : function.parameters = code.receipt.loweredParameters.map Prod.fst :=
    (FunctionCode.Parameters.of_accepted code.receipt.parametersCompiled).binders.symm
  have sourcePacked : checked.catalog.project
      (TypeSystem.Ty.productMany (function.parameters.map (fun binder : TypedBinder => binder.scheme.body))) =
      .ok (SourceCoreCompatibleCatalog.packTypes (code.receipt.loweredParameters.map Prod.snd)) := by
    simpa only [parameters, List.map_map, Function.comp_def] using packed
  have projectedFunction := code.projection
  change (do pure (checked.catalog.functionType
    (← checked.catalog.project (TypeSystem.Ty.productMany (function.parameters.map (fun binder : TypedBinder => binder.scheme.body))))
    (← checked.catalog.project function.resultType))) = _ at projectedFunction
  rw [sourcePacked, resultProjected] at projectedFunction
  simp only [bind, Except.bind, pure, Except.pure, SourceCoreCompatibleCatalog.Catalog.functionType,
    profile, ↓reduceIte, Except.ok.injEq] at projectedFunction
  exact (callable_parameters projectedFunction).1.symm

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {mapping : LocationMap} {world : StoreTyping} {function : Dynamic.Closure} {native : Value}
  {bindings : List CallableIndexedParameterCertificates.Binding} {parameterCore resultCore : Ty}

/-- Native tags authenticate only the retained native parameter/result shape. -/
theorem association_native_type
    (association : CallableIndexedOwnedStoredClosureInvocation.Association
      headers keys registry faults mapping world function native bindings parameterCore resultCore) :
    native.type = CallableContract.functionType parameterCore resultCore := by
  cases association with
  | ordinary _ _ _ _ _ _ _ _ _ typed _ _ => exact typed.type_eq
  | principal _ _ _ _ _ _ _ _ _ typed _ _ => exact typed.type_eq

/-- The selected complete static body supplies its true result projection;
the actual binder projection vector remains an independent authentic receipt. -/
theorem association_binding_pack
    (association : CallableIndexedOwnedStoredClosureInvocation.Association
      headers keys registry faults mapping world function native bindings parameterCore resultCore)
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    (projected : ∀ binding ∈ bindings,
      compiled.compatible.checked.catalog.project binding.1.scheme.body = .ok binding.2) :
    parameterCore = SourceCoreCompatibleCatalog.packTypes (bindings.map Prod.snd) := by
  cases association with
  | ordinary _ _ code _ support _ _ _ _ _ _ _ =>
    exact code_binding_pack code profile projected support.body.projection
  | principal _ _ code _ support _ _ _ _ _ _ _ =>
    exact code_binding_pack code profile projected support.body.projection

section Compiler
variable {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
  {fuel : Nat} {compilation : SourceCoreFunctions.Context} {source : TypedSource}
  {scope : SourceCoreBasic.Scope} {id callee : ExpressionId} {ids : List ExpressionId}
  {metadata : IndirectCallResolution} {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  {sourceType : TypeSystem.Ty}
  {functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed)}

/-- The actual successful callee payload and genuine callable policy fix the
compiler's two native types at exactly the selected complete association. -/
theorem compiler_parameters
    (receipt : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope
      id callee ids metadata reasonAt lowered)
    (actualFunctionType : policy.callables.functionType = CallableContract.functionType)
    (association : CallableIndexedOwnedStoredClosureInvocation.Association
      headers keys registry faults mapping world function native bindings parameterCore resultCore)
    (represented : ValueRep compiled.compatible.checked registry functions mapping world
      sourceType (.closure function) native receipt.calleeCode.type) :
    receipt.parameterType = parameterCore ∧ receipt.resultType = resultCore := by
  have actualType := represented.runtime_hasType.type_eq
  have selectedType := association_native_type association
  have accepted := receipt.callableType
  rw [actualFunctionType] at accepted
  exact callable_parameters (accepted.trans (actualType.symm.trans selectedType))

/-- The existing packing type theorem retains the actual compiler vector. -/
theorem compiler_parameter_pack
    (receipt : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope
      id callee ids metadata reasonAt lowered)
    (actualFunctionType : policy.callables.functionType = CallableContract.functionType)
    (association : CallableIndexedOwnedStoredClosureInvocation.Association
      headers keys registry faults mapping world function native bindings parameterCore resultCore)
    (represented : ValueRep compiled.compatible.checked registry functions mapping world
      sourceType (.closure function) native receipt.calleeCode.type) :
    SourceCoreCompatibleCatalog.packTypes (receipt.codes.map (·.type)) = parameterCore :=
  (CompatibleExpressionConstructorNativeTyping.packed_type receipt.codes).symm.trans
    (receipt.packedType.symm.trans (compiler_parameters receipt actualFunctionType association represented).1)

/-- Genuine selected binder projections close the native pack equality;
raw Source bundle equality and actual arity are not replaced by this result. -/
theorem compiler_binding_pack
    (receipt : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope
      id callee ids metadata reasonAt lowered)
    (actualFunctionType : policy.callables.functionType = CallableContract.functionType)
    (association : CallableIndexedOwnedStoredClosureInvocation.Association
      headers keys registry faults mapping world function native bindings parameterCore resultCore)
    (represented : ValueRep compiled.compatible.checked registry functions mapping world
      sourceType (.closure function) native receipt.calleeCode.type)
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    (projected : ∀ binding ∈ bindings,
      compiled.compatible.checked.catalog.project binding.1.scheme.body = .ok binding.2) :
    SourceCoreCompatibleCatalog.packTypes (receipt.codes.map (·.type)) =
      SourceCoreCompatibleCatalog.packTypes (bindings.map Prod.snd) :=
  (compiler_parameter_pack receipt actualFunctionType association represented).trans
    (association_binding_pack association profile projected)

end Compiler
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredNativePackReceipts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredCallSourcePrefix
/-! The successful stored-call prefix starts at the authentic original caller
heap and environment. Original Source preservation supplies callee typing,
heap validity and true extension at the actual callee success post. The real
ordered argument trace supplies the corresponding facts at its actual post.
Only an authentic selected binder receipt proves arity. Current owned rows,
body Syntax, compiler pack alignment, stage gates and nonempty argument or
output coercions remain separate. Native reflection must recover both actual
Source traces before using these receipts. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredCallSourcePrefix
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedStoredClosureArgumentReceipts

/-- Every dynamic field refers to the two actual successful Source heaps;
the independent static row and application remain attached to the parent. -/
def Receipts (source : TypedSource) (context : SourceSemantics.Context)
    (callee : ExpressionId) (ids : List ExpressionId) (metadata : IndirectCallResolution)
    (environment : Dynamic.Environment) (before calleeHeap argumentsHeap : Dynamic.Heap)
    (function : Dynamic.Closure) (arguments : List Dynamic.Value) : Prop :=
  ∃ parameter result types,
    ExpressionHasType source context callee (.function parameter result) ∧
    ExpressionsHaveTypes source context ids types ∧
    IndirectApplicationValid context metadata types parameter ∧
    Dynamic.ValueHasType context calleeHeap (.closure function) (.function parameter result) ∧
    Dynamic.HeapWellTyped context calleeHeap ∧ Dynamic.HeapTypesExtend before calleeHeap ∧
    Dynamic.EnvironmentAgrees calleeHeap context.locals environment ∧
    Dynamic.ValuesHaveTypes context argumentsHeap arguments types ∧
    Dynamic.HeapWellTyped context argumentsHeap ∧ Dynamic.HeapTypesExtend calleeHeap argumentsHeap ∧
    Dynamic.EnvironmentAgrees argumentsHeap context.locals environment ∧
    Dynamic.HeapTypesExtend before argumentsHeap ∧
    arguments.length = function.parameters.length ∧
    ∃ packed, Dynamic.ValuesPack arguments packed ∧
      Dynamic.ValueHasType context argumentsHeap packed parameter ∧
      CallableIndexedOwnedStoredClosureSourceArguments.SourceArguments function argumentsHeap arguments

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {source : TypedSource} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {environment : Dynamic.Environment} {before calleeHeap argumentsHeap : Dynamic.Heap}
  {root callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {node : ExpressionNode} {type : TypeSystem.Ty} {function : Dynamic.Closure}
  {mapping : LocationMap} {world : StoreTyping} {native : Value}
  {bindings : List CallableIndexedParameterCertificates.Binding} {parameterCore resultCore : Ty}
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {nativeDefinitions : DataEnvironment}
  {model : GenericHeap.PayloadModel catalog projects nativeDefinitions}
  {arguments : List Dynamic.Value} {nativeArguments : List Value} {calleeSize argumentsSize : Nat}

/-- Original parent typing and both actual successful measured Source children
close the callee and raw argument receipts internally. No execution law or
native-to-Source typing conversion is supplied. -/
theorem from_traces_with_arity
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context source)
    (covers : evidence.Covers context)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (heapTyped : Dynamic.HeapWellTyped context before)
    (unique : NodeOccurrencesUnique source)
    (found : source.lookupExpression? root = some node)
    (form : node.form = .call callee ids (.indirect metadata))
    (typed : ExpressionHasType source context root type)
    (empty : metadata.argumentCoercions = [])
    (arity : arguments.length = function.parameters.length)
    (calleeTrace : SourceExecutionSize.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) calleeSize
      context evidence source environment before callee (.closure function) calleeHeap)
    (argumentsTrace : SourceExecutionSize.ExpressionsEvaluate (Program.ofChecked compiled.sourceProgram) argumentsSize
      context evidence source environment calleeHeap ids arguments argumentsHeap) :
    Receipts source context callee ids metadata environment before calleeHeap argumentsHeap function arguments := by
  obtain ⟨parameter, result, types, calleeTyping, argumentsTyping, application⟩ :=
    original_facts unique found form typed
  obtain ⟨calleeTyped, calleeHeapTyped, calleeExtension⟩ :=
    wellFormed.wholeLanguagePreservation.expression context evidence source environment
      before calleeHeap callee (.closure function) (.function parameter result)
      runtime covers locals heapTyped calleeTyping calleeTrace.sound
  have calleeLocals := locals.mono calleeExtension
  obtain ⟨packed, packing, argumentsTyped, argumentsHeapTyped, argumentsExtension, packedTyped⟩ :=
    after_trace wellFormed runtime covers calleeLocals calleeHeapTyped argumentsTyping argumentsTrace
  have bundle := empty_bundle application empty
  have packedParameter : Dynamic.ValueHasType context argumentsHeap packed parameter := by
    rw [← bundle]
    exact packedTyped
  have raw := CallableIndexedOwnedStoredClosureSourceArguments.at_arguments runtime
    (calleeTyped.mono argumentsExtension) argumentsHeapTyped argumentsTyped packing bundle arity
  exact ⟨parameter, result, types, calleeTyping, argumentsTyping, application,
    calleeTyped, calleeHeapTyped, calleeExtension, calleeLocals, argumentsTyped,
    argumentsHeapTyped, argumentsExtension, calleeLocals.mono argumentsExtension,
    calleeExtension.trans argumentsExtension, arity, packed, packing, packedParameter, raw⟩

/-- The original association supplies only the actual physical arity. -/
theorem from_traces
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context source)
    (covers : evidence.Covers context)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (heapTyped : Dynamic.HeapWellTyped context before)
    (unique : NodeOccurrencesUnique source)
    (found : source.lookupExpression? root = some node)
    (form : node.form = .call callee ids (.indirect metadata))
    (typed : ExpressionHasType source context root type)
    (empty : metadata.argumentCoercions = [])
    (association : CallableIndexedOwnedStoredClosureInvocation.Association
      headers keys registry faults mapping world function native bindings parameterCore resultCore)
    (represented : CallableIndexedParameterMeaning.Arguments model mapping world bindings arguments nativeArguments)
    (calleeTrace : SourceExecutionSize.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) calleeSize
      context evidence source environment before callee (.closure function) calleeHeap)
    (argumentsTrace : SourceExecutionSize.ExpressionsEvaluate (Program.ofChecked compiled.sourceProgram) argumentsSize
      context evidence source environment calleeHeap ids arguments argumentsHeap) :
    Receipts source context callee ids metadata environment before calleeHeap argumentsHeap function arguments := by
  exact from_traces_with_arity wellFormed runtime covers locals heapTyped unique found form typed empty
    (arity_of_association association represented) calleeTrace argumentsTrace

universe u
variable {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (CallableIndexedOwnedFunctionState.Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {index : ProtectedStateTransition.Index} (initial : callerProtocol.State index)

/-- Initial Source heap admission is consumed at that exact initial state.
Owned-row admission at the later argument state remains its own real receipt. -/
theorem from_admission
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context source)
    (covers : evidence.Covers context)
    (locals : Dynamic.EnvironmentAgrees index.heap context.locals environment)
    (admitted : CallableIndexedOwnedSourceAdmission.Admission bridge context initial)
    (unique : NodeOccurrencesUnique source)
    (found : source.lookupExpression? root = some node)
    (form : node.form = .call callee ids (.indirect metadata))
    (typed : ExpressionHasType source context root type)
    (empty : metadata.argumentCoercions = [])
    (association : CallableIndexedOwnedStoredClosureInvocation.Association
      headers keys registry faults mapping world function native bindings parameterCore resultCore)
    (represented : CallableIndexedParameterMeaning.Arguments model mapping world bindings arguments nativeArguments)
    (calleeTrace : SourceExecutionSize.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) calleeSize
      context evidence source environment index.heap callee (.closure function) calleeHeap)
    (argumentsTrace : SourceExecutionSize.ExpressionsEvaluate (Program.ofChecked compiled.sourceProgram) argumentsSize
      context evidence source environment calleeHeap ids arguments argumentsHeap) :
    Receipts source context callee ids metadata environment index.heap calleeHeap argumentsHeap function arguments :=
  from_traces wellFormed runtime covers locals admitted.heap unique found form typed empty association represented
    calleeTrace argumentsTrace

/-- Current Source heap admission and actual physical arity suffice for the
original two successful Source traces, without a legacy closure association. -/
theorem from_admission_with_arity
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context source)
    (covers : evidence.Covers context)
    (locals : Dynamic.EnvironmentAgrees index.heap context.locals environment)
    (admitted : CallableIndexedOwnedSourceAdmission.Admission bridge context initial)
    (unique : NodeOccurrencesUnique source)
    (found : source.lookupExpression? root = some node)
    (form : node.form = .call callee ids (.indirect metadata))
    (typed : ExpressionHasType source context root type)
    (empty : metadata.argumentCoercions = [])
    (arity : arguments.length = function.parameters.length)
    (calleeTrace : SourceExecutionSize.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) calleeSize
      context evidence source environment index.heap callee (.closure function) calleeHeap)
    (argumentsTrace : SourceExecutionSize.ExpressionsEvaluate (Program.ofChecked compiled.sourceProgram) argumentsSize
      context evidence source environment calleeHeap ids arguments argumentsHeap) :
    Receipts source context callee ids metadata environment index.heap calleeHeap argumentsHeap function arguments :=
  from_traces_with_arity wellFormed runtime covers locals admitted.heap unique found form typed empty arity
    calleeTrace argumentsTrace

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredCallSourcePrefix
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredClosureAssociation
/-! Genuine map/world extensions carry the complete selected association from
the callee post to the argument post. Native payload, Code, binder/result row,
Support, SourceOrigin, captured Globals and body Syntax remain the same.
This static transport supplies no current caller rows or Source heap typing. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredClosureInvocation
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {mapping futureMapping : LocationMap} {world futureWorld : StoreTyping}
  {function : Dynamic.Closure} {native : Value}
  {bindings : List CallableIndexedParameterCertificates.Binding} {parameterCore resultCore : Ty}

/-- Only real map/world extensions change the representation indices.
The full same captured provenance is retained beside its unchanged payload. -/
theorem Association.extend
    (association : Association headers keys registry faults mapping world function native bindings parameterCore resultCore)
    (maps : LocationMap.Extends mapping futureMapping) (worlds : WorldExtends world futureWorld) :
    Association headers keys registry faults futureMapping futureWorld function native bindings parameterCore resultCore := by
  cases association with
  | ordinary owner captured code history support sourceOrigin prefixContext observed referenceIndex typed escaped syntaxTree =>
    exact .ordinary owner (captured.extend maps worlds) code history support sourceOrigin
      prefixContext observed referenceIndex (typed.weaken worlds) escaped syntaxTree
  | principal owner captured code history support sourceOrigin observed leading referenceIndex typed escaped syntaxTree =>
    exact .principal owner (captured.extend maps worlds) code history support sourceOrigin
      observed leading referenceIndex (typed.weaken worlds) escaped syntaxTree

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredClosureInvocation
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredApplicationProjection
/-! The pure application suffix of the original indirect call uses four
administrative environment entries. Its payload application has the same
measured body, captures, argument and stores after those pure reads. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredApplicationProjection
open Core CoreProof

/-- Preserve the exact grade while identifying only the original pure reads. -/
theorem to_payload {size : Nat} {environment : Core.Environment}
    {before after : Store} {function token argument arityToken value : Value}
    (evaluation : EvaluationSize size (arityToken :: argument :: token :: function :: environment) before
      (.apply (.second (.first (.var 3))) (.var 1)) value after) :
    EvaluationSize size [function, argument] before CallableIndexedLambdaCalls.applyPayload value after := by
  cases evaluation with
  | apply selected parameter body =>
      cases selected with
      | second tagged =>
          cases tagged with
          | first lookup =>
              cases lookup with
              | var found =>
                  simp only [List.getElem?_cons_succ, List.getElem?_cons_zero] at found
                  cases Option.some.inj found
                  cases parameter with
                  | var read =>
                      simp only [List.getElem?_cons_succ, List.getElem?_cons_zero] at read
                      cases Option.some.inj read
                      exact .apply (.second (.first (.var rfl))) (.var rfl) body

/-- Reinsert the same administrative entries without changing the body grade. -/
theorem from_payload {size : Nat} {environment : Core.Environment}
    {before after : Store} {function token argument arityToken value : Value}
    (evaluation : EvaluationSize size [function, argument] before
      CallableIndexedLambdaCalls.applyPayload value after) :
    EvaluationSize size (arityToken :: argument :: token :: function :: environment) before
      (.apply (.second (.first (.var 3))) (.var 1)) value after := by
  cases evaluation with
  | apply selected parameter body =>
      cases selected with
      | second tagged =>
          cases tagged with
          | first lookup =>
              cases lookup with
              | var found =>
                  simp only [List.getElem?_cons_zero] at found
                  cases Option.some.inj found
                  cases parameter with
                  | var read =>
                      simp only [List.getElem?_cons_succ, List.getElem?_cons_zero] at read
                      cases Option.some.inj read
                      exact .apply (.second (.first (.var rfl))) (.var rfl) body

/-- Both original expressions have identical measured completion certificates. -/
theorem measured_iff {size : Nat} {environment : Core.Environment}
    {before after : Store} {function token argument arityToken value : Value} :
    EvaluationSize size (arityToken :: argument :: token :: function :: environment) before
      (.apply (.second (.first (.var 3))) (.var 1)) value after ↔
    EvaluationSize size [function, argument] before CallableIndexedLambdaCalls.applyPayload value after :=
  ⟨to_payload, from_payload⟩

/-- The existing finite-size theorem supplies the grade for ordinary completion. -/
theorem evaluates_to_payload {environment : Core.Environment}
    {before after : Store} {function token argument arityToken value : Value}
    (evaluation : Evaluates (arityToken :: argument :: token :: function :: environment) before
      (.apply (.second (.first (.var 3))) (.var 1)) value after) :
    Evaluates [function, argument] before CallableIndexedLambdaCalls.applyPayload value after := by
  obtain ⟨size, measured⟩ := evaluation_has_size evaluation
  exact (to_payload measured).sound

/-- Completion reuses the original body and exact stores under the actual prefix. -/
theorem evaluates_from_payload {environment : Core.Environment}
    {before after : Store} {function token argument arityToken value : Value}
    (evaluation : Evaluates [function, argument] before CallableIndexedLambdaCalls.applyPayload value after) :
    Evaluates (arityToken :: argument :: token :: function :: environment) before
      (.apply (.second (.first (.var 3))) (.var 1)) value after := by
  obtain ⟨size, measured⟩ := evaluation_has_size evaluation
  exact (from_payload measured).sound

theorem evaluates_iff {environment : Core.Environment}
    {before after : Store} {function token argument arityToken value : Value} :
    Evaluates (arityToken :: argument :: token :: function :: environment) before
      (.apply (.second (.first (.var 3))) (.var 1)) value after ↔
    Evaluates [function, argument] before CallableIndexedLambdaCalls.applyPayload value after :=
  ⟨evaluates_to_payload, evaluates_from_payload⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredApplicationProjection
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredFunctionModelReceipts
/-! The actual stored-call witnesses retain an explicit function model.
These receipts contain the original value, heap, owned-state and intermediate
effects. Gate and application-prefix certificates remain in their original
modules. No closure classifier or execution producer is asserted here. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredFunctionModelReceipts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectSourceAdapters
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (functionModel : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope id callee ids metadata reasonAt lowered)
  {native : SourceCoreGeneralFunctions.CallableContext} (prepared : Prepared compiler native)
  {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment} {calleeNode : ExpressionNode}
  {firstMap : LocationMap} {firstWorld : StoreTyping} {before : Dynamic.Heap} {firstStore : Store}
  {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
  (first : callerProtocol.State ⟨scope, firstMap, firstWorld, before, firstStore, canonical⟩)
  {sourceTypes : List TypeSystem.Ty} {calleeHeap : Dynamic.Heap} {calleeStore : Store}
  {calleeNative : Value} {calleeMap : LocationMap} {calleeWorld : StoreTyping}

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functionModel

/-- The original full parent post at its actual returned owned state. -/
def ParentResultAt (outcome : Dynamic.ExpressionOutcome) (after : Dynamic.Heap) (value : Value) (finalStore : Store)
    (finalMap : LocationMap) (finalWorld : StoreTyping) : Prop :=
  GenericExpressionMeaning.ResultRepresents model finalMap finalWorld compiler.original.type lowered.type faults outcome value ∧
  CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functionModel finalMap finalWorld after finalStore ∧
  LocationMap.Extends firstMap finalMap ∧ WorldExtends firstWorld finalWorld ∧
  AdministrativePreserved firstMap firstStore finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
  ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
    callerProtocol.Relates first reached ∧ PostAdmission bridge context compiler.original.type outcome reached

/-- One actual successful callee child, with its full representation. -/
def ValuePost (sourceValue : Dynamic.Value) (after : Dynamic.Heap) (value : Value) (finalStore : Store)
    (finalMap : LocationMap) (finalWorld : StoreTyping) : Prop :=
  Evaluates actual firstStore (compiler.calleeCode.expression.rename ξ) (.inRight .word value) finalStore ∧
  ValueRep compiled.compatible.checked registry functionModel finalMap finalWorld calleeNode.type sourceValue value compiler.calleeCode.type ∧
  CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functionModel finalMap finalWorld after finalStore ∧
  LocationMap.Extends firstMap finalMap ∧ WorldExtends firstWorld finalWorld ∧
  AdministrativePreserved firstMap firstStore finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
  ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
    callerProtocol.Relates first reached ∧ PostAdmission bridge context calleeNode.type (.value sourceValue) reached

/-- Actual argument success keeps both intermediate and cumulative effects,
beside the whole fourth-bind trace and its strict grade. -/
def SuccessStep (budget : Nat) (value : Value) (finalStore : Store) : Prop :=
  ∃ nativeSize sourceSize sources values after argumentStore finalMap finalWorld,
    EvaluationSize nativeSize (.unit :: calleeNative :: actual) calleeStore
      ((((SourceCoreCalls.packArguments compiler.codes).expression.rename ξ).weakenAt 0).weakenAt 0)
      (.inRight .word (DataPatternValues.packValues values)) argumentStore ∧ nativeSize < budget ∧
    SourceExecutionSize.ExpressionsEvaluate (Program.ofChecked compiled.sourceProgram) sourceSize
      context evidence source environment calleeHeap ids sources after ∧
    DataExpressionSequence.Values model finalMap finalWorld sourceTypes (compiler.codes.map (·.type)) sources values ∧
    CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functionModel finalMap finalWorld after argumentStore ∧
    LocationMap.Extends calleeMap finalMap ∧ WorldExtends calleeWorld finalWorld ∧
    AdministrativePreserved calleeMap calleeStore finalMap argumentStore ∧ Dynamic.HeapMetadataExtend calleeHeap after ∧
    LocationMap.Extends firstMap finalMap ∧ WorldExtends firstWorld finalWorld ∧
    AdministrativePreserved firstMap firstStore finalMap argumentStore ∧ Dynamic.HeapMetadataExtend before after ∧
    (∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, argumentStore, canonical⟩,
      callerProtocol.Relates first reached ∧ Admission bridge context reached) ∧
    (∃ remainingSize,
      EvaluationSize remainingSize (DataPatternValues.packValues values :: .unit :: calleeNative :: actual) argumentStore
        (LanguageResult.bind compiler.resultType
          (CallableContract.dispatch prepared.site.gates .beforeApplication native.diagnostics.unknown (.second (.var 2)))
          (.apply (.second (.first (.var 3))) (.var 1))) value finalStore ∧
      remainingSize < budget)

/-- A token relation is kept only at the actual fault post. The caller chooses
the genuine relation for child faults or selected physical arity rejection. -/
def FaultPost (tokens : Dynamic.SemanticFault → Word → Prop)
    (reason : Dynamic.SemanticFault) (after : Dynamic.Heap) (token : Word) (finalStore : Store)
    (finalMap : LocationMap) (finalWorld : StoreTyping) : Prop :=
  tokens reason token ∧
  CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functionModel finalMap finalWorld after finalStore ∧
  LocationMap.Extends firstMap finalMap ∧ WorldExtends firstWorld finalWorld ∧
  AdministrativePreserved firstMap firstStore finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
  ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
    callerProtocol.Relates first reached ∧ PostAdmission bridge context compiler.original.type (.fault reason) reached

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredFunctionModelReceipts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedExtendedReadyMethodInvocationBounds
/-! Genuine method selections and original parameter receipts select their
strict body child from the extended joint family. Actual invocation preserves
the reached body pool through the saved-frame write. Source and native sizes
remain independent; the existing measured method cores are reused. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedExtendedReadyMethodInvocationBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedOwnedFunctionState CallablePreparedMethodRuntimeMeaning
open CallableIndexedParameterCertificates CallableIndexedParameterMeaning
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}

variable {headerCertificates : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) →
    SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {headerSyntax : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) → ExpressionId → Prop}

variable {method : ExecutableImplMethods.CheckedMethod}
  (principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method)
  {administrative : Core.Context}
  {expressionSyntax : ExpressionId → Prop} {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {validity : SourceSemantics.Context → Prop} {diagnosticPolicy : AssignmentDiagnosticPolicy}
  (profile : CallablePreparedMethodCatalogHookMeaning.ProfileFor principal.cached.compilation (.initial compiled.compatible.checked)
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed) principal.sourceBody principal.dictionary administrative registry faults
    expressionSyntax certificates validity diagnosticPolicy)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (escaped : faults .controlEscapedFunction principal.cached.compilation.own.table.escapedReason)
  (extend : ∀ {context next binder}, validity context → BinderExtends principal.sourceBody.source.owner context binder next → validity next)
  (runtimeOf : ∀ {context}, validity context →
    CompatibleRuntimeContextValidity.Valid principal.named.specialized.function.solvedRequirements context principal.dictionary)
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {callerEnvironment : Environment} {arguments : List Dynamic.Value} {payloads : List Value}
  (installed : Installed principal.cached.compilation (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (sourceBody := principal.sourceBody)
    (administrative := administrative) functions mapping world before store callerEnvironment)
  {callerScope : SourceCoreLocalCell.Scope} {callerCanonical : Environment}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (caller : State headers keys ⟨callerScope, mapping, world, before, store, callerCanonical⟩)

  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (beforeTyped : Dynamic.HeapWellTyped principal.sourceFunction.context before)
  (argumentsTyped : Dynamic.ValuesHaveTypes principal.sourceFunction.context before arguments profile.types)
  (stable : CallableIndexedOwnedIndirectExpressionHeads.StableRows caller)
  (observed : CallableIndexedOwnedExpressionHeads.Globals (headers := headers) owner 0 [] installed.canonical)

variable (syntaxTree : GenericImperativeMatch.Syntax principal.sourceFunction.source expressionSyntax profile.context
    (.statements true principal.sourceFunction.body) principal.sourceFunction.resultType)

include wellFormed beforeTyped argumentsTyped stable observed syntaxTree in
theorem source_continuation (budget : Nat)
    (below : CallableIndexedOwnedExtendedJointReadyContinuations.PreservingBelow
      (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := headerCertificates) (expressionSyntax := headerSyntax) functions wellFormed budget) :
    CallableIndexedOwnedMethodInvocationBounds.SourceContinuationWithHistory
      (program := Program.ofChecked compiled.sourceProgram) (headers := headers) (keys := keys)
      (arguments := arguments) (payloads := payloads) (owner := owner) (caller := caller)
      principal.cached.compilation profile functions escaped extend runtimeOf installed budget := by
  exact CallableIndexedOwnedMethodReadyFamilyReceipts.source_continuation
    principal profile functions escaped extend runtimeOf installed owner caller wellFormed
    beforeTyped argumentsTyped stable observed syntaxTree budget (fun index => below (.existing (.method index)))

include wellFormed beforeTyped argumentsTyped stable observed syntaxTree in
theorem native_continuation (budget : Nat)
    (below : CallableIndexedOwnedExtendedJointReadyContinuations.ReflectingBelow
      (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := headerCertificates) (expressionSyntax := headerSyntax) functions wellFormed budget) :
    CallableIndexedOwnedMethodInvocationBounds.NativeContinuationWithHistory
      (program := Program.ofChecked compiled.sourceProgram) (headers := headers) (keys := keys)
      (arguments := arguments) (payloads := payloads) (owner := owner) (caller := caller)
      principal.cached.compilation profile functions escaped extend runtimeOf installed budget := by
  exact CallableIndexedOwnedMethodReadyFamilyReceipts.native_continuation
    principal profile functions escaped extend runtimeOf installed owner caller wellFormed
    beforeTyped argumentsTyped stable observed syntaxTree budget (fun index => below (.existing (.method index)))

variable (represented : Arguments (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
    mapping world principal.named.inputs arguments payloads)
  (sameFrame : installed.frameLocation = owner.key.frameLocation)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions mapping world before store)

include escaped extend runtimeOf wellFormed beforeTyped argumentsTyped stable observed syntaxTree represented sameFrame heaps in
theorem invocation_preserves_at (budget : Nat)
    (below : CallableIndexedOwnedExtendedJointReadyContinuations.PreservingBelow
      (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := headerCertificates) (expressionSyntax := headerSyntax) functions wellFormed budget)
    {size : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.BodyOutcome (Program.ofChecked compiled.sourceProgram) size principal.sourceBody principal.dictionary before arguments outcome after)
    (within : size ≤ budget) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates (DataPatternValues.packValues payloads :: installed.captured) store
        (principal.cached.compilation.output.rename installed.embedding.lift) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        finalMap finalWorld principal.sourceBody.resultType principal.named.signature.resultType faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ProtectedStateTransition.Transition (protocol headers keys) caller
        ⟨callerScope, finalMap, finalWorld, after, finalStore, callerCanonical⟩ := by
  exact CallableIndexedOwnedMethodInvocationBounds.invocation_preserves_bounded_at_with_history
    principal.cached.compilation profile functions escaped extend runtimeOf installed represented owner caller sameFrame heaps budget
    (source_continuation principal profile functions escaped extend runtimeOf installed owner caller
      wellFormed beforeTyped argumentsTyped stable observed syntaxTree budget below)
    trace within

include escaped extend runtimeOf wellFormed beforeTyped argumentsTyped stable observed syntaxTree represented sameFrame heaps in
theorem invocation_reflects_at (budget : Nat)
    (below : CallableIndexedOwnedExtendedJointReadyContinuations.ReflectingBelow
      (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := headerCertificates) (expressionSyntax := headerSyntax) functions wellFormed budget)
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size (DataPatternValues.packValues payloads :: installed.captured) store
      (principal.cached.compilation.output.rename installed.embedding.lift) value finalStore) (within : size ≤ budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.BodyOutcome (Program.ofChecked compiled.sourceProgram) sourceSize principal.sourceBody principal.dictionary before arguments outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        finalMap finalWorld principal.sourceBody.resultType principal.named.signature.resultType faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ProtectedStateTransition.Transition (protocol headers keys) caller
        ⟨callerScope, finalMap, finalWorld, after, finalStore, callerCanonical⟩ := by
  exact CallableIndexedOwnedMethodInvocationBounds.invocation_reflects_bounded_at_with_history
    principal.cached.compilation profile functions escaped extend runtimeOf installed represented owner caller sameFrame heaps budget
    (native_continuation principal profile functions escaped extend runtimeOf installed owner caller
      wellFormed beforeTyped argumentsTyped stable observed syntaxTree budget below)
    completed within

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedExtendedReadyMethodInvocationBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedExtendedJointReadyFamilyBounds
/-! This finite connection uses the existing measured Ready Family for the
authentic additive joint indices. Its expression selectors receive only the
strictly smaller dependent body meanings and must be supplied by the actual
expression dispatcher. The module does not close that mixed dispatcher. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedExtendedJointReadyFamilyBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedOwnedFunctionState
open CallableIndexedOwnedAdmittedLexicalReadiness (readiness)
open CallableIndexedOwnedExtendedJointReadyFamilyInputs

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {certificates : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) →
    SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {expressionSyntax : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) → ExpressionId → Prop}

variable (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))

/-- The actual source expression dispatcher receives strictly smaller joint
body meanings at each callee's own protocol, full origin and genuine facts. -/
abbrev PreservingExpressions : Prop :=
  ∀ index : Index (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax),
    ∀ context, (origin index).validity context → ∀ budget child, child ≤ budget →
      (∀ callee : Index (headers := headers) (keys := keys) (registry := registry) (faults := faults)
          (certificates := certificates) (expressionSyntax := expressionSyntax), RecursiveNamedBoundedContracts.Below budget
        (CallableRuntimeBodyReadyOrigins.PreservesAt (protocol callee) (readiness (bridge callee))
          (CallableIndexedOwnedAllocationProducer.StableOwner keys) (inputs wellFormed callee).facts
          functions (Program.ofChecked compiled.sourceProgram) (origin callee))) →
      RecursiveNamedLexicalContracts.Stateful.WithReady.ExpressionPreservesAt (protocol index) (readiness (bridge index))
        (Program.ofChecked compiled.sourceProgram) (origin index).function.evidence
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        (inputs wellFormed index).exprFacts ((origin index).certificates context)
        (context := context) (source := (origin index).function.source) (faults := faults) child

/-- Native expression children retain the original strict dependent callee
bounds and independently reconstructed Source grades at the actual post. -/
abbrev ReflectingExpressions : Prop :=
  ∀ index : Index (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax),
    ∀ context, (origin index).validity context → ∀ budget child, child ≤ budget →
      (∀ callee : Index (headers := headers) (keys := keys) (registry := registry) (faults := faults)
          (certificates := certificates) (expressionSyntax := expressionSyntax), RecursiveNamedBoundedContracts.Below budget
        (CallableRuntimeBodyReadyOrigins.ReflectsAt (protocol callee) (readiness (bridge callee))
          (CallableIndexedOwnedAllocationProducer.StableOwner keys) (inputs wellFormed callee).facts
          functions (Program.ofChecked compiled.sourceProgram) (origin callee))) →
      RecursiveNamedLexicalContracts.Stateful.WithReady.ExpressionReflectsAt (protocol index) (readiness (bridge index))
        (Program.ofChecked compiled.sourceProgram) (origin index).function.evidence
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        (inputs wellFormed index).exprFacts ((origin index).certificates context)
        (context := context) (source := (origin index).function.source) (faults := faults) child

variable (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
  (sameLayouts : ∀ header, header ∈ headers → header.layouts = compiled.indexed.layouts)

include extension faithful observations sameLayouts in
/-- The sole existing measured Family composes genuine finite catalog kits
with this source dispatcher; all actual reached entry fields remain intact. -/
theorem preserves_at
    (expressions : PreservingExpressions (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax) functions wellFormed)
    (size : Nat) : ∀ index : Index (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax),
    CallableRuntimeBodyReadyOrigins.PreservesAt (protocol index) (readiness (bridge index))
      (CallableIndexedOwnedAllocationProducer.StableOwner keys) (inputs wellFormed index).facts
      functions (Program.ofChecked compiled.sourceProgram) (origin index) size := by
  exact CallableRuntimeBodyMutualMeaning.Stateful.WithReady.Family.preserves_at (registry := registry) (faults := faults)
    origin functions (Program.ofChecked compiled.sourceProgram)
    protocol (fun _ => CallableIndexedOwnedAllocationProducer.StableOwner keys)
    (producer functions sameLayouts) (acquire functions sameLayouts) transport bindings
    (fun index => readiness (bridge index)) (inputs wellFormed) expressions
    (fun index budget children => preserving_kits functions sameLayouts wellFormed extension faithful observations
      index budget children) size

include extension faithful observations sameLayouts in
/-- The same Family consumes original native completions and preserves the
independent Source grade and each branch's actual returned protocol witness. -/
theorem reflects_at (functionTypes : FunctionRuntimeViews functions)
    (expressions : ReflectingExpressions (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax) functions wellFormed)
    (size : Nat) : ∀ index : Index (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax),
    CallableRuntimeBodyReadyOrigins.ReflectsAt (protocol index) (readiness (bridge index))
      (CallableIndexedOwnedAllocationProducer.StableOwner keys) (inputs wellFormed index).facts
      functions (Program.ofChecked compiled.sourceProgram) (origin index) size := by
  exact CallableRuntimeBodyMutualMeaning.Stateful.WithReady.Family.reflects_at (registry := registry) (faults := faults)
    origin functions (Program.ofChecked compiled.sourceProgram)
    protocol (fun _ => CallableIndexedOwnedAllocationProducer.StableOwner keys)
    (producer functions sameLayouts) (acquire functions sameLayouts) transport bindings
    (fun index => readiness (bridge index)) (inputs wellFormed) expressions
    (fun index budget children => reflecting_kits functions sameLayouts wellFormed extension faithful observations
      functionTypes index budget children) size

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedExtendedJointReadyFamilyBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedExtendedReadyNamedExpressionCallerBounds
/-! Ordinary and direct named runtime expressions use the existing support
fold at the genuine caller protocol. Each authentic nested parameter entry
selects its strict body child from the extended joint family, retaining the
original principal packet and every caller facet through actual restoration. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedExtendedReadyNamedExpressionCallerBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedLexicalReadiness (readiness)
open CallableIndexedOwnedNamedNestedReadyFamilyReceipts (body_protocol bridge origin Index)
open CallableIndexedOwnedExpressionHeads (Globals)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry}
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (prefixZero : owner.key.capturePrefix = 0)
  (globalCounts : ∀ header, header ∈ headers → header.globals = compiled.indexed.base.globals.length)
  {compilation : SourceCoreFunctions.Context}
  {certificates : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) → SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {expressionSyntax : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) → ExpressionId → Prop}

variable {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (caller : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
    (fun index => Globals (headers := headers) owner compilation.administrativePrefix index.scope index.canonical)
    callerProtocol)
  (transport : ProtectedStateTransition.AdministrativeTransport callerProtocol)

variable {source : TypedSource} {context : SourceSemantics.Context} (evidence : Dynamic.EvidenceEnvironment)
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word} {fuel : Nat}
  {faults : FunctionCalls.FaultRep}
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram)) (sourceRuntime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context source)
  (covers : evidence.Covers context) (unique : NodeOccurrencesUnique source)
  (owners : ((Program.ofChecked compiled.sourceProgram).functions.map (fun definition => definition.body.owner)).Nodup)
  (idsUnique : RequirementIdsUnique context)
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))
  (sameLayouts : ∀ header, header ∈ headers → header.layouts = compiled.indexed.layouts)
  (escaped : ∀ header, header ∈ headers → faults .controlEscapedFunction header.escaped)
  (profiles : ∀ header, header ∈ headers → CallableIndexedOwnedAdmittedNamedExpressionHeads.ProfilesFor
    (headers := headers) (owner := owner) (functions := functions) (registry := registry) (faults := faults)
    (certificates := certificates) (expressionSyntax := expressionSyntax)
    (diagnosticPolicy := .reachable) (runtime := true) header)
  (syntaxTrees : ∀ header, header ∈ headers → GenericImperativeMatch.Syntax header.function.source
    (expressionSyntax header) header.context (.statements true header.function.body) header.function.resultType)

include prefixZero globalCounts transport extension faithful observations functionTypes wellFormed sourceRuntime covers unique owners idsUnique
  uninitialized missing sameLayouts escaped profiles syntaxTrees in
theorem preserves_at_runtime (sameLedger : context.solvedRequirements = solved)
    (runtimeLedger : RuntimeRequirementLedgerValid context) (budget size : Nat) (within : size ≤ budget)
    (below : CallableIndexedOwnedExtendedJointReadyContinuations.PreservingBelow
      (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax) functions wellFormed budget) :
    CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      (CallableIndexedOwnedIndirectCallerProtocol.forget_slots caller)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) context evidence source
      (CallableIndexedOwnedReadyNestedNamedExpressionCallerBounds.RuntimeTree (headers := headers)
        (compilation := compilation) (source := source) (context := context) (solved := solved)
        (reasonAt := reasonAt) (fuel := fuel) evidence) faults size := by
  exact CallableIndexedOwnedReadyNestedNamedExpressionCallerBounds.preserves_at_runtime
    functions extension faithful observations functionTypes owner prefixZero globalCounts caller transport evidence
    wellFormed sourceRuntime covers unique owners idsUnique uninitialized missing sameLayouts escaped profiles syntaxTrees
    sameLedger runtimeLedger budget size within (fun index => below (.namedNested index))

include prefixZero globalCounts transport extension faithful observations functionTypes wellFormed sourceRuntime covers unique
  uninitialized missing sameLayouts escaped profiles syntaxTrees in
theorem reflects_at_runtime (sameLedger : context.solvedRequirements = solved)
    (runtimeLedger : RuntimeRequirementLedgerValid context) (budget size : Nat) (within : size ≤ budget)
    (below : CallableIndexedOwnedExtendedJointReadyContinuations.ReflectingBelow
      (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax) functions wellFormed budget) :
    CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      (CallableIndexedOwnedIndirectCallerProtocol.forget_slots caller)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) context evidence source
      (CallableIndexedOwnedReadyNestedNamedExpressionCallerBounds.RuntimeTree (headers := headers)
        (compilation := compilation) (source := source) (context := context) (solved := solved)
        (reasonAt := reasonAt) (fuel := fuel) evidence) faults size := by
  exact CallableIndexedOwnedReadyNestedNamedExpressionCallerBounds.reflects_at_runtime
    functions extension faithful observations functionTypes owner prefixZero globalCounts caller transport evidence
    wellFormed sourceRuntime covers unique uninitialized missing sameLayouts escaped profiles syntaxTrees
    sameLedger runtimeLedger budget size within (fun index => below (.namedNested index))


end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedExtendedReadyNamedExpressionCallerBounds
end
